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

    def indexOfInt(e: T): BigInt = {
      ???[BigInt]
      
      //this match {
      //  case Cons(h, t) =>
      //    val r = t.indexOfInt(e)

      //    if (e == h) {
      //      BigInt(0)
      //    } else {
      //      if (r < 0) {
      //        r
      //      } else {
      //        r + 1
      //      }
      //    }
      //  case Nil() =>
      //    BigInt(-1)
      //}
      
    } ensuring { res =>
      if (res < 0) {
        !(content contains e)
      } else {
        res < size && apply(res) == e
      }
    }
  }

  case class Cons[T](head: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

}
