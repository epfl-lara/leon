import scala.collection.immutable.Set

import leon.lang._

object ListOperations {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

	  def content(l: List) : Set[Int] = l match {
	    case Nil() => Set.empty
	    case Cons(head, tail) => Set(head) ++ content(tail)
	  }
    
//    def isEmpty(l: List) = l match {
//	    case Nil() => true
//	    case Cons(_, _) => false      
//    }
    
    def concat(l1: List, l2: List) : List = ({
      hole(l1)
    }) ensuring(res => content(res) == content(l1) ++ content(l2))

}
