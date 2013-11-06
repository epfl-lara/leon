//import scala.collection.immutable.Set
import leon.Utils._

object MergeSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  case class Pair(fst:List,snd:List)
  
  def log()

  /*def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }*/

  /*def is_sorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x,xs) => xs match {
      case Nil() => true
      case Cons(y, ys) => x <= y && is_sorted(Cons(y, ys))
    }
  }*/    
  
   def mult(x : Int, y : Int) : Int = {
    require(x >= 0 && y >= 0)
      if(x == 0 || y == 0) 0
      else 
        mult(x-1,y) + y
    } ensuring(res => res >= mult(x/2,y) + mult(x/2,y))

  def length(list:List): Int = list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + length(xs)
  }

  def splithelper(aList:List,bList:List,n:Int): Pair = {
    require(n >= 0)
    
    if (n <= 0) Pair(aList,bList)
    else
	bList match {
    	      case Nil() => Pair(aList,bList)
    	      case Cons(x,xs) => splithelper(Cons(x,aList),xs,n-1)
	}
  } ensuring(res => length(res.fst) <= length(alist) + n  
		  				&& length(res.snd) <= length(blist) - n))
  //ensuring(res => true template((a,b,c) => a*length(res.fst) +b*length(alist) +c*n <= 0 
      //&& length(res.snd) <= length(blist) - n))

  def split(list:List,n:Int): Pair = splithelper(Nil(),list,n)

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
  }) ensuring(res => true template((a,b,x) => time <= a*length(alist) + b*length(blist) + c))
  //ensuring(res => contents(res) == contents(aList) ++ contents(bList))

  def mergeSort(list:List):List = (list match {
    case Nil() => list
    case Cons(x,Nil()) => list
    case _ =>
    	 val p = split(list,length(list)/2)
   	 merge(mergeSort(p.fst), mergeSort(p.snd))
   	 
  }) ensuring(res => length(res) == length(list) 
      && template((a,b,c) => time <= a*mult(length(list),log(length(list)) + b*length(list) +c))
  //ensuring(res => contents(res) == contents(list) && is_sorted(res))
 

  /*def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))
  
    println(ls)
    println(mergeSort(ls))
  }*/
}
