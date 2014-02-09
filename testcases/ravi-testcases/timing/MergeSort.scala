//import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object MergeSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  //case class Pair(fst:List,snd:List)
  
  @monotonic
  def log(x: Int) : Int = {
    //require(x >= 0)    
    if(x <= 1) 0
    else 1 + log(x/2)    
  } //ensuring(res=> true template((b) => res >= b))
  
  def size(list:List): Int = {list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + size(xs)
  }} ensuring(res => res >= 0)
  
  def length(l:List): Int = {
    l match {
      case Nil() => 0
      case Cons(x,xs) => 1 + length(xs)
    }
  } ensuring(res => res >= 0 && res == size(l) template((a,b) => time <= a*size(l) + b))

  def split(l:List,n:Int): (List,List) = {
    require(n >= 0 && n <= size(l))    
    if (n <= 0) (Nil(),l)
    else
	l match {
      case Nil() => (Nil(),l)
      case Cons(x,xs) => {
        if(n == 1) (Cons(x,Nil()), xs)
        else {
          val (fst,snd) = split(xs, n-1)
          (Cons(x,fst), snd)
        }        
      }
	}
  } ensuring(res => size(res._2) == size(l) - n && size(res._1) == n template((a,b) => time <= a*n +b))

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
  }) ensuring(res => size(aList)+size(bList) == size(res) template((a,b,c) => time <= a*size(aList) + b*size(bList) + c))  

  def mergeSort(list:List):List = {
    //require(len == )  
  
    list match {      
      case Cons(x,Nil()) => list
      case Cons(_,Cons(_,_)) =>
         val lby2 = length(list)/2
    	 val (fst,snd) = split(list,lby2)     	  
      	 //merge(mergeSort(fst,l), mergeSort(snd,len - l))
    	 merge(mergeSort(fst),mergeSort(snd))
      	 
      case _ => list
   	 
  }} ensuring(res => size(res) == size(list) template((a,b,c) => time <= a*(size(list)*size(list)) + c)) 
      //template((a,b) => time <= a*size(list) + b))
    
  //ensuring(res => true template((a,b) => time <= a*(size(list)*log(size(list))) + b))   
}
