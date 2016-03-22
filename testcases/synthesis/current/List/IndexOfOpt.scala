import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object IndexOf {
  sealed abstract class List[T] {
    def size: BigInt = {
      this match {
        case Nil() => BigInt(0)
        case Cons(_, t) => BigInt(1) + t.size
      }
    } ensuring {
      res => res >= 0
    }

    def content: Set[T] = this match {
      case Nil() => Set.empty[T]
      case Cons(i, t) => Set(i) ++ t.content
    }

    def apply(i: BigInt): T = {
      require(i >= 0 && i < size)
      this match {
        case Cons(h, t) =>
          if (i == 0) {
            h
          } else {
            t.apply(i-1)
          }
      }
    } ensuring { e =>
      content contains e
    }

    def indexOfOpt(e: T): Option[BigInt] = {
      ???[Option[BigInt]]
      /*
      this match {
        case Cons(h, t) =>
          val r = t.indexOfOpt(e)

          if (e == h) {
            Some(BigInt(0))
          } else {
            r match {
              case Some(i) => Some(i+1)
              case None() => None[BigInt]()
            }
          }
        case Nil() =>
          None[BigInt]()
      }
      */
    } ensuring { res =>
      res match {
        case None() => !(content contains e)
        case Some(i) => i >= 0 && i < size && apply(i) == e
      }
    }
  }

  case class Cons[T](head: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

}
