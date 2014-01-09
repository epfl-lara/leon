import leon.Utils._

object Generics3 {
  abstract class List[T]
  case class Cons[A](head: A, tail: List[A]) extends List[A]
  case class Nil[B]() extends List[B]

  case class Container[T](_1: T)

  def c(i: Int): Container[Int] = Container(i)

  def test1(): List[Container[Int]] = {
    val list1 = Cons(Container(2), Nil())
    Cons(Container(1), list1)
  } ensuring { res => res == Cons(Container(1), Cons(Container(2), Nil())) }

  def test2(): List[Boolean] = {
    Cons(true, Cons(false, Nil()))
  } ensuring { res => res == Cons(true, Cons(false, Nil())) }

  def test3(): List[Container[Int]] = {
    Cons(c(1), Cons(c(2), Nil()))
  } ensuring { res => res == Cons(Container(1), Cons(Container(2), Nil())) }
}

// vim: set ts=4 sw=4 et:
