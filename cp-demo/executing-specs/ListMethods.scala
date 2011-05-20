import cp.Definitions._
import cp.Terms._

@spec object Specs {
  abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))
  })
}

object ListMethods {
  import Specs._

  def last(list : List) : Int = {
    val (elem, _) = ((e : Int, zs : List) => concat(zs, Cons(e, Nil())) == list).solve
    elem
  }

  def main(args: Array[String]) : Unit = {
    val l = Cons(1, Cons(2, Cons(3, Nil())))

    println("Here is a list: " + l)
    println("Here is its last element: " + last(l))
  }
}
