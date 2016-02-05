import leon.lang._
import leon.annotation._

object QuickSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  sealed abstract class OptInt
  case class Some(i: Int) extends OptInt
  case class None() extends OptInt

  def content(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => content(xs) ++ Set(x)
  }

  def contains(l: List, e: Int): Boolean = l match {
    case Nil() => false
    case Cons(x, xs) => x == e || contains(xs, e)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x,Nil()) => true
    case Cons(x,Cons(y,xs)) => x<=y && isSorted(Cons(y,xs))
  }

  def min(l: List): OptInt = l match {
    case Nil() => None()
    case Cons(x, xs) => min(xs) match {
      case Some(m) => if (x <= m) Some(x) else Some(m)
      case None() => Some(x)
    }
  }

  def max(l: List): OptInt = l match {
    case Nil() => None()
    case Cons(x, xs) => max(xs) match {
      case Some(m) => if (x >= m) Some(x) else Some(m)
      case None() => Some(x)
    }
  }

  def rev_append(aList:List,bList:List): List = (aList match {
    case Nil() => bList
    case Cons(x,xs) => rev_append(xs,Cons(x,bList))
  }) ensuring(content(_) == content(aList) ++ content(bList))

  def reverse(list:List): List = rev_append(list,Nil()) ensuring(content(_) == content(list))

  def append(aList:List,bList:List): List = (aList match {
    case Nil() => bList
    case _ => rev_append(reverse(aList),bList)
  }) ensuring(content(_) == content(aList) ++ content(bList))

  def greater(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n < x) Cons(x,greater(n,xs)) else greater(n,xs)
  }

  @induct
  def greaterProp(n: Int, list: List): Boolean = (min(greater(n, list)) match {
    case Some(m) => n < m
    case None() => true
  }) holds

  def smaller(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n>x) Cons(x,smaller(n,xs)) else smaller(n,xs)
  }

  @induct
  def smallerProp(n: Int, list: List): Boolean = (max(smaller(n, list)) match {
    case Some(m) => n > m
    case None() => true
  }) holds

  def equals(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n==x) Cons(x,equals(n,xs)) else equals(n,xs)
  }

  @induct
  def equalsProp1(n: Int, list: List): Boolean = (max(equals(n, list)) match {
    case Some(m) => n == m
    case None() => true
  }) holds

  @induct
  def equalsProp2(n: Int, list: List): Boolean = (min(equals(n, list)) match {
    case Some(m) => n == m
    case None() => true
  }) holds

  @induct
  def smallerContent(n: Int, e: Int, l: List): Boolean = {
    !(contains(l, e) && e < n) || contains(smaller(n, l),e)
  } holds

  @induct
  def greaterContent(n: Int, e: Int, l: List): Boolean = {
    !(contains(l, e) && e > n) || contains(greater(n, l),e)
  } holds

  @induct
  def equalsContent(n: Int, e: Int, l: List): Boolean = {
    !(contains(l, e) && e == n) || contains(equals(n, l),e)
  } holds

  def partitionProp(n: Int, e: Int, l: List): Boolean =
    (!contains(l, e) || (contains(smaller(n, l), e) || contains(equals(n,l), e) || contains(greater(n, l), e))) //  holds

  def quickSort(list:List): List = (list match {
    case Nil() => Nil()
    case Cons(x,Nil()) => list
    case Cons(x,xs) => append(append(quickSort(smaller(x,xs)),Cons(x,equals(x,xs))),quickSort(greater(x,xs)))
  }) ensuring(res => content(res) == content(list)) // && isSorted(res))

  @ignore
  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(quickSort(ls))
  }
}
