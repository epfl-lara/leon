import leon._
import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object ListQueue {

  case class Queue[T](in: List[T], out: List[T]) {
    def toListOut: List[T] = {
      out ++ in.reverse
    }

    def toListIn: List[T] = {
      in ++ out.reverse
    }

    def size: BigInt = {
      in.size + out.size
    } ensuring {
      _ >= 0
    }

    def content: Set[T] = {
      in.content ++ out.content
    }


    def isEmpty: Boolean = {

      ???[Boolean]

    } ensuring {
      res => res == (in == Nil[T]() && out == Nil[T]())
    }

    def enqueue(t: T): Queue[T] = {

      ???[Queue[T]] // Queue(Cons(t, in), out)

    } ensuring { res =>
      (res.size == size + 1) &&
      (res.content == content ++ Set(t)) &&
      (res.toListIn == Cons(t, toListIn))
    }

    def dequeue(): (Queue[T], T) = {
      require(in.nonEmpty || out.nonEmpty)

      out match {
        case Cons(h, t) =>
          (Queue(in, t), h)
        case Nil() =>
          Queue(Nil(), in.reverse).dequeue()
      }
    } ensuring { resAndT =>
      val res = resAndT._1
      val t   = resAndT._2

      (res.size == size - 1) &&
      (content contains t) &&
      (Cons(t, res.toListOut) == toListOut)
    }
  }
}
