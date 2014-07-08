import leon.annotation._ //import scala.collection.immutable.Set
import leon.lang._

object InsertionSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  sealed abstract class OptInt
  case class Some(value: Int) extends OptInt
  case class None() extends OptInt

  def size(l : List) : Int = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  def min(l : List) : OptInt = l match {
    case Nil() => None()
    case Cons(x, xs) => min(xs) match {
      case None() => Some(x)
      case Some(x2) => if(x < x2) Some(x) else Some(x2)
    }
  }

  def minProp0(l : List) : Boolean = { l match {
    case Nil() => true
    case c @ Cons(x, xs) => min(c) match {
      case None() => false
      case Some(m) => x >= m
    }
  }} holds

  def minProp1(l : List) : Boolean = {
    require(isSorted(l)) // && size(l) <= 5)
    l match {
      case Nil() => true
      case c @ Cons(x, xs) => min(c) match {
        case None() => false
        case Some(m) => x == m
      }
    }
  } holds


  // O(n) 
  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, xs@Cons(y, ys)) => x <= y && isSorted(xs) // Manos : changed
  }

  // O(n^2)
  def sortedIns(e: Int, l: List): List = {
    require(isSorted(l)) //  && size(l) <= 5)
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
    }
  } ensuring(res => contents(res) == contents(l) ++ Set(e) && 
    isSorted(res)
  )

  // O(n^3)
  def sort(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x,xs) => sortedIns(x, sort(xs))
  }) ensuring(res => contents(res) == contents(l) && 
    isSorted(res)
  )
/*
  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(sort(ls))
  }
*//*
  def psr (input : Int) : Int = {
    (input * 476272 + 938709) % 187987
  }
  def rec(size : Int, acc : List) : List = {
    if (size == 0) acc
    else rec(size -1, Cons(psr(size), acc))
  }
  
  def test(size : Int) : List = { 
      val l = rec(size, Nil())
      sort(l)
  }
*/

  def init() : List = Nil()
  def simpleInsert(l : List, i : Int) : List = Cons(i,l)
  def test(l : List) : List = sort(l)
  
}
