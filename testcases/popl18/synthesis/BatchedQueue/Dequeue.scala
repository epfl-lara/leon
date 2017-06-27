import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.collection._


case class Queue[T](f: List[T], r: List[T]) {
  def content: Set[T] = f.content ++ r.content
  def size: BigInt = f.size + r.size

  def isEmpty: Boolean = f.isEmpty && r.isEmpty

  def invariant: Boolean = {
    (f.isEmpty) ==> (r.isEmpty)
  }

  def toList: List[T] = f ++ r.reverse

  def dequeue: Queue[T] = {
    require(invariant && !isEmpty)
    /*
    f match {
      case Cons(_, ht) =>
        ht match {
          case Nil() => Queue(r.reverse, Nil())
          case Cons(_, _) => Queue(ht, r)
        }
    }*/

    ???[Queue[T]]
  } ensuring { (res: Queue[T]) =>
      res.size == size-1 && res.toList == this.toList.tail && res.invariant
  }
}

object Queue {
  @production(100)
  def mkQ[T](f: List[T], r: List[T]) = Queue(f, r)
  @production(10)
  def reverse[T](l: List[T]) = l.reverse
}
