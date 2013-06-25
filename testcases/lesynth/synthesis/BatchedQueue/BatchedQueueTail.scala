import scala.collection.immutable.Set

import leon.Utils._

object BatchedQueue {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List

  def content(l: List): Set[Int] = l match {
    case Nil => Set.empty
    case Cons(head, tail) => Set(head) ++ content(tail)
  }

  def content(p: Queue): Set[Int] =
    content(p.f) ++ content(p.r)

  def size(l: List): Int = l match {
    case Nil => 0
    case Cons(head, tail) => 1 + size(tail)
  }

  def size(q: Queue): Int =
    size(q.f) + size(q.r)

//  def isEmpty(p: Queue): Boolean = p.f == Nil && p.r == Nil

  case class Queue(f: List, r: List)

  def rev_append(aList: List, bList: List): List = (aList match {
    case Nil => bList
    case Cons(x, xs) => rev_append(xs, Cons(x, bList))
  }) ensuring (
    res =>
      content(res) == content(aList) ++ content(bList) &&
        size(res) == size(aList) + size(bList))

  def reverse(list: List) = rev_append(list, Nil) ensuring (
    res =>
      content(res) == content(list) && size(res) == size(list))

  def checkf(f: List, r: List): Queue = (f match {
    case Nil => Queue(reverse(r), Nil)
    case _ => Queue(f, r)
  }) ensuring {
    res =>
      content(res) == content(f) ++ content(r) &&
        size(res) == size(f) + size(r)
  }

  def head(p: Queue): List = {
    p.f match {
      case Nil => Nil
      case Cons(x, xs) => Cons(x, Nil)
    }
  }

  def correctQueue(q:Queue) = if (q.f == Nil) q.r == Nil else true
  
  def invariantList(q:Queue, f: List, r: List): Boolean = {
  	rev_append(q.f, q.r) == rev_append(f, r)
  }
    
  def merge(l1: List, l2: List): List = l1 match {
    case Nil => l2
    case Cons(a, tail) => Cons(a, merge(tail, l2))
  }
    
//    p.f match {
//      case Nil => p
//      case Cons(_, xs) => checkf(xs, p.r)
//    }
  def tail(p: Queue): List = {
    require(correctQueue(p))
    choose {
      (res: List) =>
        invariantList(p, merge(head(p), res), Nil)
    }
  }

}
