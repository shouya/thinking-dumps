package recfun
import common._

object Main {
  def main(args: Array[String]) {
    println("Pascal's Triangle")
    for (row <- 0 to 10) {
      for (col <- 0 to row)
        print(pascal(col, row) + " ")
      println()
    }
  }

  /**
   * Exercise 1
   */
  def pascal(c: Int, r: Int): Int =
    if (c == 0) 1
    else if (c == r) 1
    else pascal(c - 1, r - 1) + pascal(c, r - 1)


  /**
   * Exercise 2
   */
  def balance(chars: List[Char]): Boolean = {
    def balance_stack(rest_chars : List[Char], stack : Int) : Boolean = {
      if (rest_chars.isEmpty && stack == 0) true
      else if (stack < 0) false
      else if (rest_chars.isEmpty) false
      else if (rest_chars.head == '(') balance_stack(rest_chars.tail, stack + 1)
      else if (rest_chars.head == ')') balance_stack(rest_chars.tail, stack - 1)
      else balance_stack(rest_chars.tail, stack)
    }
    balance_stack(chars, 0)
  }

  /**
   * Exercise 3
   */
  def countChange(money: Int, coins: List[Int]): Int = {
    if (coins.isEmpty && money == 0) 1
    else if (money < 0) 0
    else if (coins.isEmpty) 0
    else countChange(money - coins.head, coins) + countChange(money, coins.tail)
  }
}
