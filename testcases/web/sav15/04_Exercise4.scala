import leon.annotation._
import leon.lang._

object InsertionSort {

  sealed abstract class Option[T]
  case class Some[T](value: T) extends Option[T]
  case class None[T]() extends Option[T]


  sealed abstract class List {
    def size: BigInt = (this match {
      case Nil() => 0
      case Cons(_, t) => 1 + t.size
    })

    def content: Set[BigInt] = this match {
      case Nil() => Set()
      case Cons(h, t) => Set(h) ++ t.content
    }

    def min: Option[BigInt] = this match {
      case Nil() => None()
      case Cons(h, t) => t.min match {
        case None() => Some(h)
        case Some(m) => if(h < m) Some(h) else Some(m)
      }
    }

    def isSorted: Boolean = this match {
      case Nil() => true
      case Cons(h, Nil()) => true
      case Cons(h1, t1 @ Cons(h2, t2)) => h1 <= h2 && t1.isSorted
    }


    /* Inserting element 'e' into a sorted list 'l' produces a sorted list with
     * the expected content and size */
    def insert(e: BigInt): List = {
      require(isSorted)
      this match {
        case Nil() => Cons(e, Nil())
        case Cons(h, t) => 
          if (h <= e) {
            Cons(h, t.insert(e))
          } else {
            Cons(e, this)
          }
      }
    }


    /* Insertion sort yields a sorted list of same size and content as the input
     * list */
    def sort: List = (this match {
      case Nil() => Nil()
      case Cons(h, t) => t.sort.insert(h)
    }) ensuring(res => res.content == this.content 
                    && res.isSorted
                    && res.size == this.size
    )

  }
  case class Cons(h: BigInt, t: List) extends List
  case class Nil() extends List


}
