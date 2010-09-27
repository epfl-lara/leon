object Demo {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List) : Int = (l match {
    case Nil() => 0
    case Cons(x, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def sz(l: List) : Boolean = {
    size(l) == 0
  } ensuring(_ == true)

  def f(x: Int) : Boolean = {
    x > 4
  } ensuring(x => x)
}
