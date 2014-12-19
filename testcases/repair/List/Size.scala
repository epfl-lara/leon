import leon._
import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object List {
  def size(l: List[Int]): Int = (l match {
    case Nil() => 1
    case Cons(h, t) => 1 + size(t)
  }) ensuring {
    (res: Int) =>
      ((l, res) passes {
        case Cons(a, Nil()) => 1
        case Cons(a, Cons(b, Nil())) => 2
        case Cons(a, Cons(b, Cons(c, Nil()))) => 3
        case Nil() => 0
      })
  }
}
