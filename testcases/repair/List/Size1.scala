import leon._
import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object List {
  def size(l: List[Int]): Int = (l match {
    case Cons(h, t) => 3 + size(t) // FIXME: 1 + ...
  }) ensuring {
    (res: Int) =>
      ((l, res) passes {
        case Cons(a, Nil()) => 1
        case Nil() => 0
      })
  }

}
