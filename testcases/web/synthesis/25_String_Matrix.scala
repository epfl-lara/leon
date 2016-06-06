import leon.lang._
import leon.annotation._
import synthesis._

object Matrix { 
  case class CList[T](head: T, tail: Option[CList[T]]) {
    def +:(el: T) = CList(el, Some(this))
  }

  // Built-in function for printing non-empty lists CList
  def clistMkString[T](in: CList[T], infix: String, f: T => String): String = {
    in match {
      case CList(head, Some(tail)) => f(head) + infix + clistMkString(tail, infix, f)
      case CList(head, None()) => f(head)
    }
  }

  /** Shows how to use custom pretty printers to pretty print a custom list of a list. */
  def CListStringToString(in: CList[CList[String]]): String = {
    ???[String]
  } ensuring {
    (res: String) => (in, res) passes {
      case CList(CList(a, Some(CList(b, None()))), Some(CList(CList(c, Some(CList(d, None()))), None()))) =>
        a + "," + b + "\n" + c + "," + d
    }
  }
  
  import leon.collection._
  
  /** Shows how to use built-in function to pretty print a list of a list as a 2D matrix. */
  def matrixToString(in : List[List[String]]): String =  {
    ???[String]
  } ensuring {
    (res : String) => (in, res) passes {
      case x if x == List(
        List("1", "2"),  
        List("3", "4")
      ) =>
"""<table border="1"><tr><td>1</td><td>2</td></tr>
<tr><td>3</td><td>4</td></tr></table>"""
    }
  }
  
  def isMatrix(in: List[List[String]], width: BigInt, height: BigInt): Boolean = {
    in match {
      case Nil() if height == 0 => true
      case Cons(row, remaining) => row.length == width && isMatrix(remaining, width, height - 1)
      case _ => false
    }
  }
  
  
  def wrongMatrixConjecture(in: List[List[String]]) = {
    require(isMatrix(in, 3, 3))
    in(0)(0) == in(0)(1) || 
    in(0)(1) == in(0)(2) || 
    in(0)(2) == in(0)(0) ||
    in(1)(0) == in(1)(1) || 
    in(1)(1) == in(1)(2) || 
    in(1)(2) == in(1)(0) ||
    in(2)(0) == in(2)(1) || 
    in(2)(1) == in(2)(2) || 
    in(2)(2) == in(2)(0)
  } holds
}
}
