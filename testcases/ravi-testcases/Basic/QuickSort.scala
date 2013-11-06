//import scala.collection.immutable.Set
import leon.Utils._

object QuickSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  def size(l:List): Int = {l match {
    case Nil() => 0
    case Cons(x,xs) => 1 + size(xs)
  }} //ensuring(_ >= 0)
  
  /*def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }*/

  /*def is_sorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x,Nil()) => true
    case Cons(x,Cons(y,xs)) => x<=y && is_sorted(Cons(y,xs))
  }*/
  
  case class Triple(fst:List,snd:List, trd: List)
  
  def mult(x : Int, y : Int) : Int = {
    require(x >= 0 && y >= 0)
      if(x == 0 || y == 0) 0
      else
    	  mult(x-1,y-1) +  x + y - 1    	  
  } //ensuring(_ >= 0)
  //ensuring(res => true template((e,f) => e*res + f <= 0))

  def rev_append(aList:List,bList:List): List = {aList match {
    case Nil() => bList
    case Cons(x,xs) => rev_append(xs,Cons(x,bList))
    
  }} ensuring(res => size(res) == size(aList) + size(bList) template((a,b) => time <= a*size(aList) +b))
  //ensuring(res => size(res) == size(aList) + size(bList) && time <= 10*size(aList) +4) 
  //ensuring(res => size(res) == size(aList) + size(bList) template((a,b) => time <= a*size(aList) +b))

  def reverse(list:List): List = rev_append(list,Nil())

  def append(aList:List,bList:List): List = aList match {
    case Nil() => bList
    case _ => rev_append(reverse(aList),bList)
    
  } 
  
/*  def greater(n:Int,l:List) : List = {l match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n < x) Cons(x,greater(n,xs)) else greater(n,xs)
    
  }} ensuring(res => size(res) <= size(l) template((a,b) => time <= a*size(l) +b)) 
  //ensuring(res => size(res) <= size(l) && time <= 11*size(l) +5) 
  //ensuring(res => size(res) <= size(l) template((a,b) => time <= a*size(l) +b))

  def smaller(n:Int,l:List) : List = {l match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n>x) Cons(x,smaller(n,xs)) else smaller(n,xs)
    
  }} ensuring(res => size(res) <= size(l) template((a,b) => time <= a*size(l) +b))
  //ensuring(res => size(res) <= size(l) && time <= 11*size(l) +5)
  //ensuring(res => size(res) <= size(l) template((a,b) => time <= a*size(l) +b))

  def equals(n:Int,l:List) : List = {l match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n==x) Cons(x,equals(n,xs)) else equals(n,xs)
    
  }} ensuring(res => size(res) <= size(l) template((a,b) => time <= a*size(l) +b)) */
  //ensuring(res => size(res) <= size(l) && time <= 11*size(l) +5) 
  
  def partition(n:Int,l:List) : Triple = (l match {
    case Nil() => Triple(Nil(), Nil(), Nil())
    case Cons(x,xs) => {
      val t = partition(n,xs)
      if (n < x) Triple(t.fst, t.snd, Cons(x,t.trd))
      else if(n == x) Triple(t.fst, Cons(x,t.snd), t.trd)
      else Triple(Cons(x,t.fst), t.snd, t.trd)
    }    
 }) ensuring(res => (size(l) == size(res.fst) + size(res.snd) + size(res.trd)) template((a,b) => time <= a*size(l) +b))     

  def quickSort(l:List): List = (l match {
    case Nil() => Nil()
    case Cons(x,Nil()) => l
    case Cons(x,xs) => {      
      val t = partition(x, xs)
      append(append(quickSort(t.fst), Cons(x, t.snd)), quickSort(t.trd))
    } 
    case _ => l
  }) ensuring(res => size(res) == size(l) template((a,b) => time <= a*mult(size(l),size(l)) +b))
  //ensuring(res => size(res) == size(l) && time <= 100*size(l)*size(l) +30)   
  //ensuring(res => size(res) == size(l) template((a,b) => time <= a*mult(size(l),size(l)) +b))   
  //ensuring(res => contents(res) == contents(list)) // && is_sorted(res))

  
/*  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(quickSort(ls))
  }*/
}
