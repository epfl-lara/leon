import scala.collection.immutable.Set

object PaperExamples {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def usize(list: List) : Int = { throw new Exception("uninterpreted") }
  def ucont(list: List) : Set[Int] = { throw new Exception("uninterpreted") }

  def intro(list: List, x: Int, xs: List) : Boolean = {
    require(
       (list == Nil() || list == Cons(x, xs))
    && (usize(Nil()) == 0 && usize(Cons(x, xs)) == 1 + usize(xs))
    && (ucont(Nil()) == Set.empty[Int] && ucont(Cons(x, xs)) == Set(x) ++ ucont(xs))
    && ucont(xs).size <= usize(xs)
    )
    ucont(list).size <= usize(list)
  } ensuring(_ == true)
}
