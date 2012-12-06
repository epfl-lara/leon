object Prog002 {
  sealed abstract class List
  case class Nil() extends List
  case class Cons(head : Int, tail : List) extends List

  def isNil(l : List) : Boolean = {
    l == Nil()
  }
}
