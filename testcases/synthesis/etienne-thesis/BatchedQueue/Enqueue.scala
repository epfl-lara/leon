import leon.lang._
import leon.lang.synthesis._

object BatchedQueue {
  sealed abstract class List[T] {
    def content: Set[T] = {
      this match {
        case Cons(h, t) => Set(h) ++ t.content
        case Nil() => Set()
      }
    }

    def size: BigInt = {
      this match {
        case Cons(h, t) => BigInt(1) + t.size
        case Nil() => BigInt(0)
      }
    } ensuring { _ >= 0 }

    def reverse: List[T] = {
      this match {
        case Cons(h, t) => t.reverse.append(Cons(h, Nil[T]()))
        case Nil() => Nil[T]()
      }
    } ensuring { res =>
      this.content == res.content
    }

    def append(r: List[T]): List[T] = {
      this match {
        case Cons(h, t) => Cons(h, t.append(r))
        case Nil() => r
      }
    }

    def tail: List[T] = {
      require(this != Nil[T]())
      this match {
        case Cons(h, t) => t
      }
    }

    def head: T = {
      require(this != Nil[T]())
      this match {
        case Cons(h, t) => h
      }
    }

    def last: T = {
      require(this != Nil[T]())
      this match {
        case Cons(h, Nil()) => h
        case Cons(h, t) => t.last
      }
    }
  }

  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  case class Queue[T](f: List[T], r: List[T]) {
    def content: Set[T] = f.content ++ r.content
    def size: BigInt = f.size + r.size

    def invariant: Boolean = {
      (f == Nil[T]()) ==> (r == Nil[T]())
    }

    def toList: List[T] = f.append(r.reverse)

    def enqueue(v: T): Queue[T] = {
      require(invariant)

      f match {
        case Cons(h, t) =>
          Queue(f, Cons(v, r))
        case Nil() =>
          Queue(Cons(v, f), Nil())
      }

    } ensuring { (res: Queue[T]) =>
        res.invariant &&
        res.toList.last == v &&
        res.content == this.content ++ Set(v)
    }
  }
}
