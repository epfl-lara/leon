object BVs {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def size(l : List) : Int = {
    l match {
      case Nil() => 0
      case Cons(_, xs) => 1 + /* for "small" counter examples: */ 2 * size(xs)
    }
  } ensuring(_ >= 0) // smallest counter-example is a list of size Integer.MAX_VALUE, could take a while to find it :)

  def mul(i : Int, j : Int) : Int = {
    require(i >= 0 && j >= 0)
    i * j
  } ensuring(res => res >= 0)
}
