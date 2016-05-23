package eagerEval

import leon._
import lang._
import collection._

object MergeSort {

  def merge[T](less: (T, T) => Boolean)(xs: List[T], ys: List[T]): List[T] = {
    (xs, ys) match {
      case (Nil(), _) => ys
      case (_, Nil()) => xs
      case (Cons(x, xtail), Cons(y, ytail)) =>
        if (less(x, y))
          x :: merge(less)(xtail, ys)
        else
          y :: merge(less)(xs, ytail)
    }
  } ensuring { res => res.content == xs.content ++ ys.content &&
                      res.size == xs.size + ys.size }

  def split[T](list: List[T]): (List[T], List[T]) = {
    list match {
      case Nil()          => (Nil(), Nil())
      case Cons(x, Nil()) => (Cons(x, Nil()), Nil())
      case Cons(x1, Cons(x2, xs)) =>
        val (s1, s2) = split(xs)
        (Cons(x1, s1), Cons(x2, s2))
    } 
  } 

  def msort[T](less: (T, T) => Boolean)(l: List[T]): List[T] = {
    l match {
      case Nil()          => Nil[T]()
      case Cons(x, Nil()) => Cons(x, Nil())
      case _ =>
        val (first, second) = split(l)
        merge(less)(msort(less)(first), msort(less)(second))
    }
  } ensuring { res => res.content == l.content && res.size == l.size }
}
