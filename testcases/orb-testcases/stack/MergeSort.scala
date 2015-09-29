import leon.invariant._
import leon.instrumentation._

import leon.annotation._

object MergeSort {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def size(list: List): BigInt = (list match {
    case Nil() => 0
    case Cons(x,xs) => 1 + size(xs)
  }) //ensuring(res => true && tmpl((a) => res >= 0))

  def length(l: List): BigInt = {
    l match {
      case Nil() => BigInt(0)
      case Cons(x,xs) => 1 + length(xs)
    }
  } ensuring(res => res == size(l) && tmpl((a,b) => stack <= a*size(l) + b))

  def split(l: List, n: BigInt): (List, List) = {
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
  } ensuring(res => size(res._2) == size(l) - n && size(res._1) == n && size(res._2) + size(res._1) == size(l) && tmpl((a,b) => stack <= a*size(l) +b))

  def merge(aList: List, bList: List): List = (bList match {
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
  }) ensuring(res => size(aList) + size(bList) == size(res) && tmpl((a,b,c) => stack <= a*size(aList) + b*size(bList) + c))

  def mergeSort(list: List): List = {
    list match {
      case Cons(x, Nil()) => list
      case Cons(_, Cons(_, _)) =>
        val lby2 = length(list) / 2
        val (fst, snd) = split(list, lby2)
        merge(mergeSort(fst), mergeSort(snd))

      case _ => list
    }
  } ensuring(res => size(res) == size(list) && tmpl((a,b) => stack <= a*size(list) + b))
}
