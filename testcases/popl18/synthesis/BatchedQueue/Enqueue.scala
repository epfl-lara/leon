import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.collection._


  case class Queue[T](f: List[T], r: List[T]) {
    def content: Set[T] = f.content ++ r.content
    def size: BigInt = f.size + r.size

    def invariant: Boolean = {
      (f == Nil[T]()) ==> (r == Nil[T]())
    }

    def toList: List[T] = f ++ r.reverse

    def enqueue(v: T): Queue[T] = {
      require(invariant)
      //f match {
      //  case Cons(_, _) => Queue(f, Cons(v, r))
      //  case Nil() => Queue(Cons(v, Nil()), r)
      //}

      ???[Queue[T]]
    } ensuring { (res: Queue[T]) =>
      res.invariant &&
      res.toList.last == v &&
      res.size == size + 1 &&
      res.content == this.content ++ Set(v)
    }
  }
object Queue {
  @production(1)
  def mkQ[T](f: List[T], r: List[T]): Queue[T] = Queue(f, r)
}
