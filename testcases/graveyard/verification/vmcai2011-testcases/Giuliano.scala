import leon.lang._

object Giuliano {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def f(x: Int) : Int = { throw new Exception("...") }

  def form1(x: Int, y: Set[Int]) : Boolean = {
    // y.contains(x.head) && y.size == x.head
    x != f(x) || f(x) == f(f(x))
  } // ensuring(_ == true)

  def form2(f: Int, n: Int, servers: Set[Int], bizServers: Set[Int], corrServers: Set[Int], s: Set[Int]) : Boolean = {
    require(
        s.subsetOf(servers)
     && s.size > f
     && servers == corrServers ++ bizServers
     && bizServers.size == f
     && servers.size == n
     && n > 3
     && f > 0
     && 3 * f < n
    )
    (corrServers ** s).size >= 1
  } ensuring(_ == true)
}

// vim: set ts=4 sw=4 et:
