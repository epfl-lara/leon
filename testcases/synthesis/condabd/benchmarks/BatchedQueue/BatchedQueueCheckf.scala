import leon.lang._
import leon.lang.synthesis._

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

  case class Queue(f: List, r: List)

  def rev_append(aList: List, bList: List): List = (aList match {
    case Nil => bList
    case Cons(x, xs) => rev_append(xs, Cons(x, bList))
  }) ensuring (content(_) == content(aList) ++ content(bList))

  def reverse(list: List) = rev_append(list, Nil) ensuring (content(_) == content(list))

  def invariantList(q:Queue, f: List, r: List): Boolean = {
  	rev_append(q.f, q.r) == rev_append(f, r) &&
    { if (q.f == Nil) q.r == Nil else true }
  }
  
  def tail(p: Queue): Queue = {
    p.f match {
      case Nil => p
      case Cons(_, xs) => checkf(xs, p.r)
    }
  }
	
//(f match {
//    case Nil => Queue(reverse(r), Nil)
//    case _ => Queue(f, r)
  def checkf(f: List, r: List): Queue = {
    choose {
      (res: Queue) =>
        invariantList(res, f, r)
    }
  }

}
