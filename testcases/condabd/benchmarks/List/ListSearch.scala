import leon.Utils._

object ListOperations {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List
    
    sealed abstract class Option
    case class Some(i: Int) extends Option
    case object None extends Option

    def content(l: List) : Set[Int] = l match {
      case Nil() => Set.empty
      case Cons(head, tail) => Set(head) ++ content(tail)
    }

    def size(l: List) : Int = l match {
      case Nil() => 0
      case Cons(head, tail) => 1 + size(tail)
    }
//    
//    def isEmpty(l: List) = l match {
//      case Nil() => true
//      case Cons(_, _) => false      
//    }
    
    
    def linearSearch(l: List, c: Int): Option = {
      l match {
        case Nil() => None
        case Cons(lHead, lTail) =>
          if (lHead == c) Some(size(l))
          else Some(linearSearch(lTail, c))
      }
    } ensuring(res => if(res > -1) atInd(l, size(l) - res) == c else !content(l).contains(c))

    def atInd(l: List, ind: Int): Int = {
      require(ind >= 0 && ind < size(l))
      
      l match {
		case Nil() => -1
		case Cons(lHead, lTail) =>
		  if (ind == 0) lHead
		  else atInd(lTail, ind - 1)	  
      }
      
    } ensuring( res =>
      if (size(l) == 0) res == -1 else content(l).contains(res)      
  )
}
