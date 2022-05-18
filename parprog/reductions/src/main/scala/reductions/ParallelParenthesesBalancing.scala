package reductions

import scala.annotation._
import org.scalameter._
import common._

object ParallelParenthesesBalancingRunner {

  @volatile var seqResult = false

  @volatile var parResult = false

  val standardConfig = config(
    Key.exec.minWarmupRuns -> 40,
    Key.exec.maxWarmupRuns -> 80,
    Key.exec.benchRuns -> 120,
    Key.verbose -> true
  ) withWarmer(new Warmer.Default)

  def main(args: Array[String]): Unit = {
    val length = 100000000
    val chars = new Array[Char](length)
    val threshold = 10000
    val seqtime = standardConfig measure {
      seqResult = ParallelParenthesesBalancing.balance(chars)
    }
    println(s"sequential result = $seqResult")
    println(s"sequential balancing time: $seqtime ms")

    val fjtime = standardConfig measure {
      parResult = ParallelParenthesesBalancing.parBalance(chars, threshold)
    }
    println(s"parallel result = $parResult")
    println(s"parallel balancing time: $fjtime ms")
    println(s"speedup: ${seqtime / fjtime}")
  }
}

object ScanLib {
  sealed abstract class TreeResA[A] { val res: A }
  case class Leaf[A](from: Int, to: Int, override val res: A) extends TreeResA[A]
  case class Node[A](l: TreeResA[A], override val res: A, r: TreeResA[A]) extends TreeResA[A]

  val threshold = 10

  def reduceSeg[A](in: Array[A], left: Int, right: Int, a0: A, f: (A,A) => A): A = {
    var a = a0
    var i = left
    while (i < right) {
      a = f(a, in(i))
      i += 1
    }
    a
  }

  def scanLeftSeg[A](in: Array[A], from: Int, to: Int, a0: A, f: (A,A)=>A, out: Array[A]) : Unit = {
    var a = a0
    var i = from
    while (i < to) {
      a = f(a, in(i))
      out(i) = a
      i += 1
    }
    a
  }

  def upsweep[A](in: Array[A], from: Int, to: Int, f: (A, A) => A) : TreeResA[A] = {
    if (to - from < threshold)
      Leaf(from, to, reduceSeg(in, from + 1, to, in(from), f))
    else {
      val mid = from + (to - from) / 2
      val (tL, tR) = parallel(
        upsweep(in, from, mid, f),
        upsweep(in, mid, to, f)
      )
      Node(tL, f(tL.res, tR.res), tR)
    }
  }

  def downsweep[A](in: Array[A], a0: A, f: (A,A) => A, t: TreeResA[A], out: Array[A]) : Unit =
    t match {
      case Leaf(from, to, res) =>
        scanLeftSeg(in, from, to, a0, f, out)
      case Node(l, _, r) => {
        val (_, _) = parallel(
          downsweep(in, a0, f, l, out),
          downsweep(in, f(a0, l.res), f, r, out)
        )
      }
    }

  def scanLeftPar[A](in: Array[A], a0: A, f: (A, A) => A, out: Array[A]) = {
    val t = upsweep(in, 0, in.length, f)
    downsweep(in, a0, f, t, out)
    out(0) = a0
  }
}

object ParallelParenthesesBalancing {

  /** Returns `true` iff the parentheses in the input `chars` are balanced.
   */
  def balance(chars: Array[Char]): Boolean = {
    def helper(loc: Int, stack: Int): Boolean = {
      if (stack < 0)           return false
      if (loc == chars.length) return stack == 0
      if (chars(loc) == '(')   return helper(loc + 1, stack + 1)
      if (chars(loc) == ')')   return helper(loc + 1, stack - 1)
      helper(loc + 1, stack)
    }

    helper(0, 0)
  }

  /** Returns `true` iff the parentheses in the input `chars` are balanced.
   */
  def parBalance(chars: Array[Char], threshold: Int): Boolean = {
//    sealed abstract class TreeResA { val res: Int }
//    case class Leaf(from: Int, to: Int, override val res: Int) extends TreeResA
//    case class Node(l: TreeResA, override val res: Int, r: TreeResA) extends TreeResA
//
//    def upsweep(from: Int, to: Int, )
//
//    def scanLeftPar[A](in: Array[A], a0: A, f: (A, A) => A, out: Array[A]) = {
//      val t = upsweep(in, 0, in.length, f)
//      downsweep(in, a0, f, t, out)
//      out(0) = a0
//    }

    def traverse(idx: Int, until: Int, npos: Int, nneg: Int): (Int, Int) = {
      var i = idx
      var (npos_, nneg_) = (npos, nneg)
      while (i < until) {
        chars(i) match {
          case '(' => npos_ += 1
          case ')' => nneg_ += 1
          case _   => {}
        }
        i += 1
      }
      (npos_, nneg_)
    }

    def reduce(from: Int, until: Int): (Int, Int) = {
      if (until - from < threshold) return traverse(from, until, 0, 0)

      val mid = from + (until - from) / 2
      val ((lpos,lneg), (rpos,rneg)) = parallel(
        { reduce(from, mid)  },
        { reduce(mid, until) }
      )

      (lpos + rpos, lneg + rneg)
    }

    reduce(0, chars.length) == (0, 0)
  }

  // For those who want more:
  // Prove that your reduction operator is associative!

}
