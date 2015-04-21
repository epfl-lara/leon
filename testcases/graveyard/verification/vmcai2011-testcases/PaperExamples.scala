import leon.lang._

object PaperExamples {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def usize(list: List) : Int = { throw new Exception("uninterpreted") }
  def ucont(list: List) : Set[Int] = { throw new Exception("uninterpreted") }

  def intro_V(list: List, x: Int, xs: List) : Boolean = {
    require(
       (list == Nil() || list == Cons(x, xs))
    && (usize(Nil()) == 0 && usize(Cons(x, xs)) == 1 + usize(xs))
    && (ucont(Nil()) == Set.empty[Int] && ucont(Cons(x, xs)) == Set(x) ++ ucont(xs))
    && ucont(xs).size <= usize(xs)
    )
    ucont(list).size <= usize(list)
  } ensuring(_ == true)

  def naive_I(a: Set[Int], b: Set[Int], c: Set[Int]) : Boolean = {
    require(
      a.size > 1
   && a.subsetOf(b)
    )
    (b ** c).size > 2
  } ensuring(_ == true)

  def decomposition_I(a: Set[Int], b: Set[Int], c: Set[Int], d: Set[Int]) : Boolean = {
    require(
      (a -- b).size > (a ** b).size
   && (b ** c ** d) == Set.empty[Int]
    )
    (b -- d).size <= (b -- c).size
  } ensuring(_ == true)
}
