import leon.lang._
import leon.annotation._
import synthesis._

object Matrix { 
  case class CList[T](head: T, tail: Option[CList[T]]) {
    def +:(el: T) = CList(el, Some(this))
  }

  def clistMkString[T](in: CList[T], infix: String, f: T => String): String = {
    in match {
      case CList(head, Some(tail)) => f(head) + infix + clistMkString(tail, infix, f)
      case CList(head, None()) => f(head)
    }
  }

  def CListStringToString(in: CList[CList[String]]): String = {
    ???[String]
  } ensuring {
    (res: String) => (in, res) passes {
      case CList(CList(a, Some(CList(b, None()))), Some(CList(CList(c, Some(CList(d, None()))), None()))) =>
        a + "," + b + "\n" + c + "," + d
    }
  }
  
  import leon.collection._
  
  def listStringToString(in : List[List[String]]): String =  {
    ???[String]
  } ensuring {
    (res : String) => (in, res) passes {
      case Cons(Cons(a, Cons(b, Nil())), Cons(Cons(c, Cons(d, Nil())), Nil())) =>
        a + "," + b + "\n" + c + "," + d
    }
  }
}
