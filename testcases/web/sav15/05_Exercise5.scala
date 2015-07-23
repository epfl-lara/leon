import leon.lang._
import leon.annotation._

object SearchList {
  sealed abstract class List[T] {
    def size: BigInt = {
      this match {
        case Nil() => BigInt(0)
        case Cons(h, t) => 1 + t.size
      }
    } ensuring { _ >= 0 }

    def content: Set[T] = {
      this match {
        case Nil() => Set()
        case Cons(h, t) => Set(h) ++ t.content
      }
    }

    def firstPosOf(v: T): BigInt = {
      this match {
        case Nil() => BigInt(-1)
        case Cons(h, t) if h == v => BigInt(0)
        case Cons(h, t) =>
          val p = t.firstPosOf(v)
          if (p >= 0) {
            p + 1
          } else {
            p
          }
      }
    } ensuring {
     res => false // TODO: Ensure that if (and only if) res is non-negative, the list contains v.

    }

    def take(n: BigInt): List[T] = {
      require(n >= 0)
      this match {
        case Nil() => Nil[T]()
        case Cons(h, t) if n == 0 => Nil[T]()
        case Cons(h, t) => Cons(h, t.take(n - 1))
      }
    } ensuring {
      res => res.size <= n
    }

    def contains(v: T): Boolean = {
      this match {
        case Nil() => false
        case Cons(h, _) if h == v => true
        case Cons(_, t) => t.contains(v)
      }
    } ensuring {
      res => res == (content contains v)
    }
  }

  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  @induct
  def wtf[T](l: List[T], v: T): Boolean = {
    !((l.contains(v)) && (l.take(l.firstPosOf(v)).contains(v))) // What is this function checking? Translate to english. Can you remove the l.contains(v) part? Why?
  }.holds
}

