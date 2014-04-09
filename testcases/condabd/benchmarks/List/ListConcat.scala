import leon.lang._
import leon.lang.synthesis._

object ListOperations {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

	  def content(l: List) : Set[Int] = l match {
	    case Nil() => Set.empty
	    case Cons(head, tail) => Set(head) ++ content(tail)
	  }
    
    def concat(l1: List, l2: List) : List = choose {
    (out : List) =>
      content(out) == content(l1) ++ content(l2)
    }

}
