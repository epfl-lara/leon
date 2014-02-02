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

  def append(aList:List,bList:List): List = {aList match {
    case Nil() => bList
    case Cons(x, xs) => Cons(x,append(xs,bList))    
  }} ensuring(res => size(res) == size(aList) + size(bList) template((a,b) => time <= a*size(aList) +b))

  def partition(n:Int,l:List) : Triple = (l match {
    case Nil() => Triple(Nil(), Nil(), Nil())
    case Cons(x,xs) => {
      val t = partition(n,xs)
      if (n < x) Triple(t.fst, t.snd, Cons(x,t.trd))
      else if(n == x) Triple(t.fst, Cons(x,t.snd), t.trd)
      else Triple(Cons(x,t.fst), t.snd, t.trd)
    }    
 }) ensuring(res => (size(l) == size(res.fst) + size(res.snd) + size(res.trd)) template((a,b) => time <= a*size(l) +b))     

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
  //ensuring(res => size(l) == size(res) template((a,b,c,d) => time <= a*(size(l)*size(l)) + c*size(l) + d)) 
}
