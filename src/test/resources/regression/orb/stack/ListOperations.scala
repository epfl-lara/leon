import leon.invariant._
import leon.instrumentation._

object ListOperations {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def size(l: List): BigInt = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })

  def reverseRec(l1: List, l2: List): List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => reverseRec(xs, Cons(x, l2))

  }) ensuring (res =>  size(l1) + size(l2) == size(res) && tmpl((a,b) => stack <= a*size(l1) + b))

  def contains(list: List, elem: BigInt): Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => x == elem || contains(xs, elem)

  }) ensuring (res => tmpl((a,b) => stack <= a*size(list) + b))

  def distinct(l: List): List = (
    l match {
      case Nil() => Nil()
      case Cons(x, xs) => {
        val newl = distinct(xs)
        if (contains(newl, x)) newl
        else Cons(x, newl)
      }
   }) ensuring (res => size(l) >= size(res) && tmpl((a,b) => stack <= a*size(l) + b))
}
