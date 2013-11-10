import leon.Utils._

object ListOperations {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List): Int = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })

  def append(l1: List, l2: List): List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => Cons(x, append(xs, l2))

  }) ensuring (res => true template ((a, b, c) => a * size(l1) + b * size(l2) + c * size(res) == 0))

  def reverseRec(l1: List, l2: List): List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => reverseRec(xs, Cons(x, l2))

  }) ensuring (res => true template ((p, q, r) => p * size(l1) + q * size(l2) + r * size(res) == 0))

  def reverse(l: List): List = {
    reverseRec(l, Nil())
  } ensuring (res => size(l) == size(res))

  def reverse2(l: List): List = {
    l match {
      case Nil() => l
      case Cons(hd, tl) => append(reverse2(tl), Cons(hd, Nil()))
    }
  } ensuring (res => size(res) == size(l))

  def remove(elem: Int, l: List): List = {
    l match {
      case Nil() => Nil()
      case Cons(hd, tl) => if (hd == elem) remove(elem, tl) else Cons(hd, remove(elem, tl))
    }
  } 

  def contains(list: List, elem: Int): Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => x == elem || contains(xs, elem)
  }) ensuring (res => true)

  def distinct(l: List): List = (
    l match {
      case Nil() => Nil()
      case Cons(x, xs) => {
        val newl = distinct(l)
        if (contains(newl, x)) newl
        else Cons(x, newl)
      }
    })
}
