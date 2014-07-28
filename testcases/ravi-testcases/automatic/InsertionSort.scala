import leon.lang.invariantLang._

object InsertionSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  def size(l : List) : Int = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  })    

  def sortedIns(e: Int, l: List): List = {   
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
    } 
  } //ensuring(res => true template((a,b,c) => a*size(res) + b*size(l) +c == 0))

  def sort(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x,xs) => sortedIns(x, sort(xs))
    
  }) ensuring(res => size(res) == size(l))
}
