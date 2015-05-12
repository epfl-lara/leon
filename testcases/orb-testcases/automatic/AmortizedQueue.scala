import leon.lang.invariantLang._

object AmortizedQueue {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  case class Queue(front : List, rear : List)

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  })


  def qsize(q : Queue) : Int = size(q.front) + size(q.rear)

  def asList(q : Queue) : List = concat(q.front, reverse(q.rear))

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))

  }) //ensuring (res => size(res) == size(l1) + size(l2))

  def isAmortized(q : Queue) : Boolean = size(q.front) >= size(q.rear)

  def isEmpty(queue : Queue) : Boolean = queue match {
    case Queue(Nil(), Nil()) => true
    case _ => false
  }

  def reverseRec(l1: List, l2: List): List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => reverseRec(xs, Cons(x, l2))

  }) //ensuring (res =>  size(l1) + size(l2) == size(res))

  def reverse(l: List): List = {
    reverseRec(l, Nil())
  } //ensuring (res => size(l) == size(res))

  def amortizedQueue(front : List, rear : List) : Queue = {
    if (size(rear) <= size(front))
      Queue(front, rear)
    else
      Queue(concat(front, reverse(rear)), Nil())
  }

  def enqueue(q : Queue, elem : Int) : Queue = ({

    amortizedQueue(q.front, Cons(elem, q.rear))

  }) ensuring(res =>  qsize(res) == qsize(q) + 1)


  def removeLast(l : List) : List = {
    require(l != Nil())
    l match {
      case Cons(x,Nil()) => Nil()
      case Cons(x,xs) => Cons(x, removeLast(xs))
      case _ => Nil()
    }
  }

  def pop(q : Queue) : Queue = {
    require(isAmortized(q) && !isEmpty(q))
    q match {
     case Queue(front, Cons(r,rs)) => Queue(front, rs)
     case Queue(front, rear) => Queue(removeLast(front), rear)
     case _ => Queue(Nil(),Nil())
    }
  } ensuring(res =>  qsize(res) == qsize(q) - 1)
}
