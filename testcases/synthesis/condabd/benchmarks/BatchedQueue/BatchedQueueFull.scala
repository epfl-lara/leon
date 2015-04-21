import leon.lang._
import leon.collection._

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

    def size(l: List) : Int = l match {
      case Nil => 0
      case Cons(head, tail) => 1 + size(tail)
    }
  
    def size(q: Queue) : Int = 
      size(q.f) + size(q.r)
  
  def isEmpty(p: Queue): Boolean = p.f == Nil

  case class Queue(f: List, r: List)

  def rev_append(aList: List, bList: List): List = (aList match {
    case Nil => bList
    case Cons(x, xs) => rev_append(xs, Cons(x, bList))
  }) ensuring (
    res =>
      content(res) == content(aList) ++ content(bList) &&
      size(res) == size(aList) + size(bList)
  )
  
  def invariantList(q:Queue, f: List, r: List): Boolean = ({
  	rev_append(q.f, q.r) == rev_append(f, r)
  }) ensuring (
    res =>
      true
	)

  def reverse(list: List) = rev_append(list, Nil) ensuring (
    res =>
      content(res) == content(list) && size(res) == size(list)
  )

  def checkf(f: List, r: List): Queue = (f match {
    case Nil => Queue(reverse(r), Nil)
    case _ => Queue(f, r)
  }) ensuring {
    res => content(res) == content(f) ++ content(r) &&
    size(res) == size(f) + size(r) &&
    invariantList(res, f, r)
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
    require(!isEmpty(p))
    p.f match {
      case Nil => p
      case Cons(_, xs) => checkf(xs, p.r)
    }
  } ensuring {
    (res: Queue) => content(res) ++ head(p) == content(p) &&
    (if (isEmpty(p)) true
    else size(res) + 1 == size(p))
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
    checkf(p.f, Cons(x, p.r)) ensuring (
      res =>
        content(res) == content(p) ++ Set(x) &&
      size(res) == size(p) + 1 &&
          (
            if (isEmpty(p)) true
            else (content(tail(res)) ++ Set(x) == content(tail(res)) &&
        	  size(res.f) == size(p.f))
          )
    )

}
