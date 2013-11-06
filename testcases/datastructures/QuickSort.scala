//import scala.collection.immutable.Set
import leon.Utils._

object QuickSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  /*def size(l:List): Int = list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + length(xs)
  } */
  
  def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  def is_sorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x,Nil()) => true
    case Cons(x,Cons(y,xs)) => x<=y && is_sorted(Cons(y,xs))
  }

  def rev_append(aList:List,bList:List): List = aList match {
    case Nil() => bList
    case Cons(x,xs) => rev_append(xs,Cons(x,bList))
    
  } 

  def reverse(list:List): List = rev_append(list,Nil())

  def append(aList:List,bList:List): List = aList match {
    case Nil() => bList
    case _ => rev_append(reverse(aList),bList)
  }

  def greater(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n < x) Cons(x,greater(n,xs)) else greater(n,xs)
    
  }

  def smaller(n:Int,l:List) : List = l match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n>x) Cons(x,smaller(n,xs)) else smaller(n,xs)
    
  } 

  def equals(n:Int,l:List) : List = l match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n==x) Cons(x,equals(n,xs)) else equals(n,xs)    
  } 

  def quickSort(l:List): List = (l match {
    case Nil() => Nil()
    case Cons(x,Nil()) => l
    case Cons(x,xs) => {
      val res1 = quickSort(smaller(x,xs))
      val res2 = quickSort(greater(x,xs))
      append(append(res1,Cons(x,equals(x,xs))),res2)
    } 
    
  }) ensuring(res => contents(res) == contents(l) && is_sorted(res))

  
/*  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(quickSort(ls))
  }*/
}
