package orb

import leon._
import invariant._
import instrumentation._

object AmortizedQueue {
  sealed abstract class List {
    val size: BigInt = this match {
      case Nil()       => 0
      case Cons(_, xs) => 1 + xs.size
    }
  }
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def length(l: List): BigInt = {
    l match {
      case Nil()       => BigInt(0)
      case Cons(_, xs) => 1 + length(xs)
    }
  } ensuring(res => res >= 0 && alloc <= ?)

  def concat(l1: List, l2: List): List = (l1 match {
    case Nil()       => l2
    case Cons(x, xs) => Cons(x, concat(xs, l2))

  }) ensuring (res => res.size == l1.size + l2.size && alloc <= ? * l1.size + ?)

  def reverseRec(l1: List, l2: List): List = (l1 match {
    case Nil()       => l2
    case Cons(x, xs) => reverseRec(xs, Cons(x, l2))
  }) ensuring (res => l1.size + l2.size == res.size && alloc <= ? * l1.size + ?)

  def listRev(l: List): List = {
    reverseRec(l, Nil())
  } ensuring (res => l.size == res.size && alloc <= ? * l.size + ?)

  def removeLast(l: List): List = {
    require(l != Nil())
    l match {
      case Cons(x, Nil()) => Nil()
      case Cons(x, xs)    => Cons(x, removeLast(xs))
      case _              => Nil()
    }
  } ensuring (res => res.size <= l.size && tmpl((a, b) => alloc <= a * l.size + b))

  case class Queue(front: List, rear: List) {
    def qsize: BigInt = front.size + rear.size

    def asList: List = concat(front, listRev(rear))

    def isAmortized: Boolean = length(front) >= length(rear)

    def isEmpty: Boolean = this match {
      case Queue(Nil(), Nil()) => true
      case _                   => false
    }

    def amortizedQueue(front: List, rear: List): Queue = {
      if (length(rear) <= length(front))
        Queue(front, rear)
      else
        Queue(concat(front, listRev(rear)), Nil())
    }

    def enqueue(elem: BigInt): Queue = ({
      amortizedQueue(front, Cons(elem, rear))
    }) ensuring (_ => alloc <= ? * qsize + ?)

    def dequeue: Queue = {
      require(isAmortized && !isEmpty)
      front match {
        case Cons(f, fs) => amortizedQueue(fs, rear)
        case _           => Queue(Nil(), Nil())
      }
    } ensuring (_ => alloc <= ? * qsize + ?)

    def head: BigInt = {
      require(isAmortized && !isEmpty)
      front match {
        case Cons(f, _) => f
      }
    }

    def reverse: Queue = { // this lets the queue perform deque operation (but they no longer have efficient constant alloc amortized bounds)
      amortizedQueue(rear, front)
    }
  }
}
