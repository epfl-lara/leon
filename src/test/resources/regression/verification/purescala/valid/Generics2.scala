import leon.Utils._

object Generics2 {
  abstract class List[T]
  case class Cons[A](head: A, tail: List[A]) extends List[A]
  case class Nil[B]() extends List[B]

  def map[C,D](f: (C) => D, list: List[C]): List[D] = list match {
    case Cons(head, tail) => Cons(f(head), map(f, tail))
    case Nil() => Nil()
  }

  def test(): List[Boolean] = {
    val list1 = Cons(1, Cons(2, Cons(3, Nil())))
    map((x: Int) => x == 2, list1)
  } ensuring { res => res == Cons(false, Cons(true, Cons(false, Nil()))) }

}

// vim: set ts=4 sw=4 et:
