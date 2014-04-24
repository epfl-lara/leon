//import scala.collection.immutable.Set
import leon.lang.invariantLang._
import leon.annotations._

object MergeSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  def size(list:List): Int = {list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + size(xs)
  }} ensuring(res => res >= 0)
  
  def length(l:List): Int = {
    l match {
      case Nil() => 0
      case Cons(x,xs) => 1 + length(xs)
    }
  } ensuring(res => res >= 0 && res == size(l) template((a,b) => depth <= a*size(l) + b))

  def split(l:List,n:Int): (List,List) = {
    require(n >= 0 && n <= size(l))    
    if (n <= 0) (Nil(),l)
    else
	l match {
      case Nil() => (Nil(),l)
      case Cons(x,xs) => {
        val (fst,snd) = split(xs, n-1)
        (Cons(x,fst), snd)
      }
	}
  } ensuring(res => size(res._2) == size(l) - n && size(res._1) == n template((a,b) => depth <= a*n +b))
  
  def merge(aList:List, bList:List):List = (bList match {       
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
  }) ensuring(res => size(aList)+size(bList) == size(res) template((a,b,c) => depth <= a*size(aList) + b*size(bList) + c))  

  def mergeSort(list:List):List = (list match {
    case Nil() => list
    case Cons(x,Nil()) => list
    case _ =>
    	 val (fst,snd) = split(list,length(list)/2)    	 
   	     merge(mergeSort(fst), mergeSort(snd))
   	 
  }) ensuring(res => size(res) == size(list) template((a,b) => depth <= a*size(list) + b))   
}
