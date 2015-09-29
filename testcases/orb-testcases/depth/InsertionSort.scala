import scala.collection.immutable.Set
import leon.instrumentation._
import leon.invariant._


object InsertionSort {
  sealed abstract class List
  case class Cons(head:BigInt,tail:List) extends List
  case class Nil() extends List

  def size(l : List) : BigInt = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  })

  def sortedIns(e: BigInt, l: List): List = {
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
    }
  } ensuring(res => size(res) == size(l) + 1 && tmpl((a,b) => depth <= a*size(l) +b))

  def sort(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x,xs) => sortedIns(x, sort(xs))

  }) ensuring(res => size(res) == size(l) && tmpl((a,b) => depth <= a*(size(l)*size(l)) +b))
}
