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

  def splithelper(aList : List, bList : List, n : Int) : Pair = {
    if (n <= 0) Pair(aList,bList)
    else
	bList match {
    	      case Nil() => Pair(aList,bList)
    	      case Cons(x,xs) => splithelper(Cons(x,aList),xs,n-1)
	}
  } ensuring(res => contents(aList) ++ contents(bList) == contents(res.fst) ++ contents(res.snd))

//  def split(list : List, n : Int): Pair = {
//    splithelper(Nil(),list,n)
//  } ensuring(res => contents(list) == contents(res.fst) ++ contents(res.snd))
  
  def split(list: List): Pair = {
    splithelper(Nil(),list,size(list)/2)
  } ensuring(res => contents(list) == contents(res.fst) ++ contents(res.snd))

  def merge(aList : List, bList : List) : List = {
    require(isSorted(aList) && isSorted(bList))
    bList match {       
      case Nil() => aList
      case Cons(x,xs) =>
        aList match {
              case Nil() => bList
              case Cons(y,ys) =>
               if (y < x)
                  Cons(y,merge(ys, bList))
               else
                  Cons(x,merge(aList, xs))               
        }   
    }
  } ensuring(res => contents(res) == contents(aList) ++ contents(bList) && isSorted(res))

  def isEmpty(list: List) : Boolean = list match {
    case Nil() => true
    case Cons(x,xs) => false
  }
  
  def sort(list : List) : List =
      list match {
    case Nil() => list
    case Cons(_,Nil()) => list
    case _ => {
    	 val p = split(list)
	    choose {(res : List) =>
	      contents(res) == contents(list) && isSorted(res)
    	 }
    }
  }
      
//      merge(mergeSort(split(list).fst), mergeSort(split(list).snd))  
  
  //ensuring(res => contents(res) == contents(list) && isSorted(res))
 
}
