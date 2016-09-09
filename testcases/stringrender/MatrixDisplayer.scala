import leon.lang._
import leon.math._
import leon.proof.check
import leon.collection._
import leon.annotation._
import synthesis._

object MatrixDisplayer {
  
  def maxLength(a: List[String], init: BigInt): BigInt = a match {
    case Nil() => init
    case Cons(a, tail) =>  maxLength(tail, max(a.bigLength, init))
  }
  
  def maximum(a: List[BigInt], init: BigInt): BigInt = a match {
    case Nil() => init
    case Cons(a, tail) => maximum(tail, max(a, init))
  }
  
  def repeat(c: String, n: BigInt): String = {
    if(n <= 0) ""
    else if(n % 2 == 1) {
      c + repeat(c+c, (n-1)/2)
    } else {
      repeat(c+c, n/2)
    }
  }

  def padCenter(c: String, n: BigInt, char: String, oddLeftChar: String, oddRightChar: String): String = {
    val b = c.bigLength
    if(b >= n) c
    else {
      val remaining = n-b
      val half = remaining / 2
      val padder = repeat(char, half)
      if(remaining%2 == 0) {
        padder + c + padder
      } else {
        padder + oddLeftChar + c + oddRightChar + padder
      }
    }
  }
  def horizontalDelimiter(row: List[String], cellWidth: BigInt, inlineChar: String, repeatChar: String) = {
    List.mkString[String](row, inlineChar, (elem : String) => repeat(repeatChar, cellWidth))
  }
  def printrow(row: List[String], cellWidth: BigInt, leftDelimiter: String, midDelimiter: String, rightDelimiter: String, padChar: String, padOddLeft: String, padOddRight: String) = {
    leftDelimiter + List.mkString[String](row, midDelimiter,
          (elem : String) => padCenter(elem, cellWidth, padChar, padOddLeft, padOddRight)) + rightDelimiter
  }

  def showMatrix(a : List[List[Int]]): String =  {
    require(a.length > BigInt(0) && a.head.length > BigInt(0))
    val b = a.map[List[String]]((l : List[Int]) => l.map[String]((i : Int) => i.toString))
    val cellWidth = maximum(b.map[BigInt]((l : List[String]) => maxLength(l, BigInt(1))), BigInt(1))
    val width = a.head.length
    "\r\n+" + horizontalDelimiter(b.head, cellWidth, "+", "-") + "+\r\n" + List.mkString[List[String]](b, "+" + horizontalDelimiter(b.head, cellWidth, "+", "-") + "+\r\n", (row : List[String]) => printrow(row, cellWidth, "|", "|", "|\r\n", " ", "", " ")) + "+" + horizontalDelimiter(b.head, cellWidth, "+", "-") + "+"
  } ensuring {
    (res : String) => (a, res) passes {
      case x if x == List[List[Int]](List[Int](1, 234), List[Int](5674, 23)) =>
        """
/----+----\
| 1  |234 |
+----+----+
|5674| 23 |
\----+----/"""
    }
  }
  
  def test = showMatrix(List(List(1, 234), List(5674, 23)))
}
