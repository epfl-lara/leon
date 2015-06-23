import leon.invariant._
import leon.instrumentation._

object InsertionSort {
  sealed abstract class List
  case class Cons(head: BigInt, tail:List) extends List
  case class Nil() extends List

  def size(l : List) : BigInt = (l match {
    case Cons(_, xs) => 1 + size(xs)
    case _ => 0
  })

  def sortedIns(e: BigInt, l: List): List = {
    l match {
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
      case _ => Cons(e,Nil())
    }
  } ensuring(res => size(res) == size(l) + 1 && tmpl((a,b) => time <= a*size(l) +b && depth <=  a*size(l) +b))

  def sort(l: List): List = (l match {
    case Cons(x,xs) => sortedIns(x, sort(xs))
    case _ => Nil()

  }) ensuring(res => size(res) == size(l) && tmpl((a,b) => time <= a*(size(l)*size(l)) +b && rec <= a*size(l) + b))
}
