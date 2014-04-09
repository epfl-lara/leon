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
    
    def isEmpty(l: List) =  l match {
	    case Nil() => true
	    case Cons(head, tail) => false
	  }
    
    def isEmptyBad(l: List) =  l match {
	    case Nil() => true
	    case Cons(head, tail) => true
	  }
    
    def hasContent(l: List) = l match {
	    case Nil() => false
	    case Cons(head, tail) => true
	  } 
      
//      !content(l).isEmpty
    
    def concat(l1: List, l2: List) : List = choose {
    (out : List) =>
      content(out) == content(l1) ++ content(l2)
    }

}
