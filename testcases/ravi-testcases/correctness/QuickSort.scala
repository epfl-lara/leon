//import scala.collection.immutable.Set
import leon.Utils._

object QuickSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  def size(l:List): Int = {l match {
    case Nil() => 0
    case Cons(x,xs) => 1 + size(xs)
  }} 
  
  case class Triple(fst:List,snd:List, trd: List)

  def rev_append(aList:List,bList:List): List = {aList match {
    case Nil() => bList
    case Cons(x,xs) => rev_append(xs,Cons(x,bList))
    
  }} ensuring(res => true template((a,b,c) => a*size(res) + b*size(aList) + c*size(bList) == 0))
  
  def reverse(list:List): List = rev_append(list,Nil())

  def append(aList:List,bList:List): List = aList match {
    case Nil() => bList
    case _ => rev_append(reverse(aList),bList)
    
  } 
  
  def partition(n:Int,l:List) : Triple = (l match {
    case Nil() => Triple(Nil(), Nil(), Nil())
    case Cons(x,xs) => {
      val t = partition(n,xs)
      if (n < x) Triple(t.fst, t.snd, Cons(x,t.trd))
      else if(n == x) Triple(t.fst, Cons(x,t.snd), t.trd)
      else Triple(Cons(x,t.fst), t.snd, t.trd)
    }    
 }) ensuring(res => true template((a,b,c,d) => a*size(l) + b*size(res.fst) + c*size(res.snd) + d*size(res.trd) == 0))     

  def quickSort(l:List): List = (l match {
    case Nil() => Nil()
    case Cons(x,Nil()) => l
    case Cons(x,xs) => {      
      val t = partition(x, xs)
      append(append(quickSort(t.fst), Cons(x, t.snd)), quickSort(t.trd))
    } 
    case _ => l
  }) ensuring(res => size(res) == size(l)) 
}
