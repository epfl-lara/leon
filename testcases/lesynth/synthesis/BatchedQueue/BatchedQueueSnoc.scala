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

  def isEmpty(p: Queue): Boolean = p.f == Nil

  case class Queue(f: List, r: List)

  def rev_append(aList: List, bList: List): List = (aList match {
    case Nil => bList
    case Cons(x, xs) => rev_append(xs, Cons(x, bList))
  }) ensuring (content(_) == content(aList) ++ content(bList))

  def reverse(list: List) = rev_append(list, Nil) ensuring (content(_) == content(list))

  def checkf(f: List, r: List): Queue = (f match {
    case Nil => Queue(reverse(r), Nil)
    case _ => Queue(f, r)
  }) ensuring {
    res => content(res) == content(f) ++ content(r)
  }

  def head(p: Queue): Set[Int] = (
    p.f match {
      case Nil => Set[Int]()
      case Cons(x, xs) => Set(x)
    }) ensuring (
      res =>
        if (isEmpty(p)) true
        else content(p) == res ++ content(tail(p)))

  def tail(p: Queue): Queue = {
    p.f match {
      case Nil => p
      case Cons(_, xs) => checkf(xs, p.r)
    }
  }
  //	  
  //	  def last(p: Queue): Int = {
  //	    require(!isEmpty(p))
  //	    p.r match {
  //	      case Nil => reverse(p.f).asInstanceOf[Cons].head
  //	      case Cons(x, _) => x
  //	    }
  //	  }

  def snoc(p: Queue, x: Int): Queue =
    choose { (res: Queue) =>
      content(res) == content(p) ++ Set(x) &&
        (if (isEmpty(p)) true
        else content(tail(res)) ++ Set(x) == content(tail(res)))
    }

  def main(args: Array[String]): Unit = {
    val pair = Queue(Cons(4, Nil), Cons(3, Nil))

    println(head(pair))
    println(content(pair) == head(pair) ++ content(tail(pair)))

    println(head(Queue(Nil, Nil)))
  }
}
