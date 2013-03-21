import scala.collection.immutable.Set

import leon.Utils._

object ListOperations {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

//	  def content(l: List) : Set[Int] = l match {
//	    case Nil() => Set.empty
//	    case Cons(head, tail) => Set(head) ++ content(tail)
//	  }
	  def content(l: List) : Set[Int] = l match {
	    case Nil() => Set.empty
	    case Cons(head, tail) => Set(head) ++ content(tail)
	  }
    
	  def size(l: List) : Int = l match {
	    case Nil() => 0
	    case Cons(head, tail) => 1 + size(tail)
	  }
    
    def isEmpty(l: List) = l match {
	    case Nil() => true
	    case Cons(_, _) => false      
    }
    
    def concat(l1: List, l2: List) : List = ({
      
      l1 match {
        case Nil() => l2
        case Cons(l1Head, l1Tail) =>
          l1 match {
            case Nil() => l2
            case _ => Cons(l1Head, Cons(l1Head, concat(l1Tail, l2)))
          }
      }

    }) ensuring(res => 
      content(res) == content(l1) ++ content(l2) &&
      size(res) == size(l1) + size(l2)
    )

}
