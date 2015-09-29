import leon.invariant._
import leon.instrumentation._
import leon.annotation._

object Sort {
  sealed abstract class List
  case class Cons(head:BigInt,tail:List) extends List
  case class Nil() extends List

  //case class Pair(fst:List,snd:List)

  // @monotonic
  def log(x: BigInt) : BigInt = {
    //require(x >= 0)
    if(x <= 1) 0
    else 1 + log(x/2)
  } //ensuring(res=> true && tmpl((b) => res >= b))

  def size(list:List): BigInt = {list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + size(xs)
  }}

  def length(l:List): BigInt = {
    l match {
      case Nil() => 0
      case Cons(x,xs) => 1 + length(xs)
    }
  } ensuring(res => res == size(l) && tmpl((a,b) => time <= a*size(l) + b))

  def split(l:List,n:BigInt): (List,List) = {
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
  } ensuring(res => size(res._2) == size(l) - n && size(res._1) == n && tmpl((a,b) => time <= a*n +b))

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
  }) ensuring(res => size(aList)+size(bList) == size(res) && tmpl((a,b,c) => time <= a*size(aList) + b*size(bList) + c))

  def mergeSort(list:List, len: BigInt):List = {
    require(len == size(list))

    list match {
      case Cons(x,Nil()) => list
      case Cons(_,Cons(_,_)) =>
         val l = len/2
    	 val (fst,snd) = split(list,l)
      	 merge(mergeSort(fst,l), mergeSort(snd,len - l))

      case _ => list

  }} //ensuring(res => size(res) == size(list) && tmpl((a,b,c) => time <= a*(size(list)*size(list)) + c))
      //&& tmpl((a,b) => time <= a*size(list) + b))
  //ensuring(res => true && tmpl((a,b) => time <= a*(size(list)*log(size(list))) + b))
  case class Triple(fst:List,snd:List, trd: List)

  def append(aList:List,bList:List): List = {aList match {
    case Nil() => bList
    case Cons(x, xs) => Cons(x,append(xs,bList))
  }} ensuring(res => size(res) == size(aList) + size(bList) && tmpl((a,b) => time <= a*size(aList) +b))

  def partition(n:BigInt,l:List) : Triple = (l match {
    case Nil() => Triple(Nil(), Nil(), Nil())
    case Cons(x,xs) => {
      val t = partition(n,xs)
      if (n < x) Triple(t.fst, t.snd, Cons(x,t.trd))
      else if(n == x) Triple(t.fst, Cons(x,t.snd), t.trd)
      else Triple(Cons(x,t.fst), t.snd, t.trd)
    }
 }) ensuring(res => (size(l) == size(res.fst) + size(res.snd) + size(res.trd)) && tmpl((a,b) => time <= a*size(l) +b))

 //Unable to prove n^2  upper bound :-(
  def quickSort(l:List): List = (l match {
    case Nil() => Nil()
    case Cons(x,Nil()) => l
    case Cons(x,xs) => {
      val t = partition(x, xs)
      append(append(quickSort(t.fst), Cons(x, t.snd)), quickSort(t.trd))
    }
    case _ => l
  })

  def sortedIns(e: BigInt, l: List): List = {
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
    }
  } ensuring(res => size(res) == size(l) + 1 && tmpl((a,b) => time <= a*size(l) +b))

  def sort(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x,xs) => sortedIns(x, sort(xs))

  }) ensuring(res => size(res) == size(l) && tmpl((a,b) => time <= a*(size(l)*size(l)) +b))

}
