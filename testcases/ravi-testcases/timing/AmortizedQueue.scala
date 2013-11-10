import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object AmortizedQueue {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class AbsQueue
  case class Queue(front : List, rear : List) extends AbsQueue

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) 
  
  def qsize(q : AbsQueue) : Int = q match {
    case Queue(front : List, rear : List) => size(front) + size(rear)
  } 

  def asList(queue : AbsQueue) : List = queue match {
    case Queue(front, rear) => concat(front, reverse(rear))
  }

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))
  }) ensuring (res => true template((a,b,c) => a*size(res) + b*size(l1) + c*size(l2) == 0))

  def isAmortized(queue : AbsQueue) : Boolean = queue match {
    case Queue(front, rear) => size(front) >= size(rear)
  }

  def isEmpty(queue : AbsQueue) : Boolean = queue match {
    case Queue(Nil(), Nil()) => true
    case _ => false
  }

  def reverse(l : List) : List = (l match {
    case Nil() => Nil()
    case Cons(x, xs) => concat(reverse(xs), Cons(x, Nil()))
  }) ensuring (res => true template((a,b,c) => a*size(l) + b*size(res) +c == 0))

  def amortizedQueue(front : List, rear : List) : AbsQueue = {
    if (size(rear) <= size(front))
      Queue(front, rear)
    else
      Queue(concat(front, reverse(rear)), Nil())
  } 

  def enqueue(queue : AbsQueue, elem : Int) : AbsQueue = (queue match {
    case Queue(front, rear) => amortizedQueue(front, Cons(elem, rear))
    case _ => Queue(Nil(),Nil())
    
  }) ensuring(res => qsize(res) == qsize(queue) + 1)

  def dequeue(queue : AbsQueue) : AbsQueue = {
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, fs), rear) => amortizedQueue(fs, rear)
      case _ => Queue(Nil(),Nil())
    }
  } ensuring(res => qsize(res) == qsize(queue) - 1)
  
  def removeLast(l : List) : List = {
    require(l != Nil())
    l match {
      case Cons(x,Nil()) => Nil()
      case Cons(x,xs) => Cons(x, removeLast(xs))
      case _ => Nil()
    }
  } ensuring(res => true template((a,b,c) => a*size(res) + b*size(l) + c == 0))
  
  def pop(q : AbsQueue) : AbsQueue = {
    require(isAmortized(q) && !isEmpty(q))
    q match {
     case Queue(front, Cons(r,rs)) => Queue(front, rs)
     case Queue(front, rear) => Queue(removeLast(front), rear)
     case _ => Queue(Nil(),Nil())
    }
  } ensuring(res => qsize(res) == qsize(q) - 1)
}
