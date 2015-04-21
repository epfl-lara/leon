import leon.lang._
import leon.lang.synthesis._

object MergeSort {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class PairAbs
  case class Pair(fst : List, snd : List) extends PairAbs

  def contents(l : List) : Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  def isSorted(l : List) : Boolean = l match {
    case Nil() => true
    case Cons(x,xs) => xs match {
      case Nil() => true
      case Cons(y, ys) => x <= y && isSorted(Cons(y, ys))
    }
  }    

  def size(list : List) : Int = list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + size(xs)
  }

  def merge(aList : List, bList : List) : List = {
    require(isSorted(aList) && isSorted(bList))
    choose( (res: List) =>
    	contents(res) == contents(aList) ++ contents(bList) && isSorted(res)
  	)
  }

//  def merge(aList : List, bList : List) : List = {
//    require(isSorted(aList) && isSorted(bList))
//    
//    bList match {       
//      case Nil() => aList
//      case Cons(x,xs) =>
//        aList match {
//              case Nil() => bList
//              case Cons(y,ys) =>
//               if (y < x)
//                  Cons(y,merge(ys, bList))
//               else
//                  Cons(x,merge(aList, xs))               
//        }   
//    }
//  } ensuring(res => contents(res) == contents(aList) ++ contents(bList) && isSorted(res))

}
