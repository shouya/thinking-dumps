package quickcheck

import common._

import org.scalacheck._
import Arbitrary._
import Gen._
import Prop._

abstract class QuickCheckHeap extends Properties("Heap") with IntHeap {

  lazy val genHeap: Gen[H] = oneOf(
    const(empty),
    for {
      k <- arbitrary[A]
      m <- oneOf(const(empty), genHeap)
    } yield insert(k, m)
  )

  implicit lazy val arbHeap: Arbitrary[H] = Arbitrary(genHeap)

  property("gen1") = forAll { (h: H) =>
    val m = if (isEmpty(h)) 0 else findMin(h)
    findMin(insert(m, h)) == m
  }

  property("min1") = forAll { a: Int =>
    val h = insert(a, empty)
    findMin(h) == a
  }

  property("min2") = forAll { (a: Int, b: Int) =>
    val h = insert(a, insert(b, empty))
    findMin(h) == (a min b)
  }

  property("empty1") = forAll { (a: Int) =>
    val h = insert(a, empty)
    isEmpty(deleteMin(h))
  }

  def isOrdered(seq: Seq[A]): Boolean = {
    seq.zip(seq.tail).forall { case (a: A, b: A) => ord.lteq(a, b) }
  }

  def heapToList(heap: H): List[A] = {
    if (isEmpty(heap)) List.empty
    else findMin(heap) :: heapToList(deleteMin(heap))
  }

  property("order1") = forAll { h: H =>
    isOrdered(heapToList(h))
  }

  property("order2") = forAll { (a: Int, h: H) =>
    isOrdered(heapToList(insert(a, h)))
  }

  property("len1") = forAll { (a: Int, h: H) =>
    val l1 = heapToList(h).length
    val l2 = heapToList(insert(a, h)).length
    (l1 + 1) == l2
  }

  property("len2") = forAll { (a: Int, h: H) =>
    val l1 = heapToList(h).length
    if (l1 == 0)
      true
    else {
      val l2 = heapToList(deleteMin(h))
      (l1 - 1) == l2
    }
  }

  property("min3") = forAll { (a: H, b: H) =>
    val m1 = findMin(a)
    val m2 = findMin(b)
    meld(a, b) == ord.min(m1, m2)
  }

  property("len3") = forAll { (a: H, b: H) =>
    val l1 = heapToList(a).length
    val l2 = heapToList(b).length
    heapToList(meld(a, b)).length == l1 + l2
  }

  property("len0") = forAll { (_: Unit) =>
    heapToList(empty).length == 0
  }

  property("empty2") = forAll { (_: Unit) =>
    isEmpty(meld(empty, empty))
  }
}
