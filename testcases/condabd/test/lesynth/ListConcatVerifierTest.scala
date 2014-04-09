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
    
    def goodConcat1(l1: List, l2: List) : List = 
      l1 match {
        case Nil() => l2
        case Cons(l1Head, l1Tail) =>
          l1 match {
            case Nil() => l2
            case _ => Cons(l1Head, Cons(l1Head, concat(l1Tail, l2)))
          }
      }
    
    def goodConcat2(l1: List, l2: List) : List = 
      l1 match {
        case Nil() => l2
        case Cons(l1Head, l1Tail) =>
          Cons(l1Head, Cons(l1Head, concat(l1Tail, l2)))
      }
        
    def badConcat1(l1: List, l2: List) : List = 
      l1 match {
        case Nil() => l1
        case Cons(l1Head, l1Tail) =>
          Cons(l1Head, Cons(l1Head, concat(l1Tail, l2)))
      }

}
