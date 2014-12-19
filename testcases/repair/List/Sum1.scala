import leon._
import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object List {
  def sum(l: List[Int]): Int = (l match {
    case Nil() => 0
    case Cons(h, t) => 1 + sum(t) // FIXME: 1 instead of h
  }) ensuring {
    (res: Int) =>
      ((l, res) passes {
        case Cons(a, Nil()) => a
        case Cons(a, Cons(b, Nil())) => a+b
        case Cons(a, Cons(b, Cons(c, Nil()))) => a+b+c
        case Nil() => 0
      })
  }
}
