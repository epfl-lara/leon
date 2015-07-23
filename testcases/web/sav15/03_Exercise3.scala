import leon.lang._
import leon.annotation._

object ListWithSize {
    sealed abstract class List[T] {
      def size: BigInt = {
        this match {
          case Cons(h, t) => 1 + t.size
          case Nil() => BigInt(0)
        }
      } // TODO: Add appropriate post-condition

      def sizeTailRec: BigInt = sizeTailRec0(0)

      def sizeTailRec0(acc: BigInt): BigInt = {
        require(acc >= 0)
        this match {
          case Cons(h, t) => t.sizeTailRec0(acc + 1)
          case Nil() => acc
        }
      }  // TODO: Add appropriate post-condition

      // Verify
      def zip[U](that: List[U]): List[(T, U)] = {
        // TODO: Add appropriate pre-condition
        this match {
          case Nil() => Nil[(T,U)]()
          case Cons(h1, t1) => that match {
            case Cons(h2, t2) => Cons((h1, h2), t1.zip(t2))
          }
        }
      } ensuring(_.size == this.size)


      def content: Set[T] = this match {
        case Nil() => Set()
        case Cons(h, t) => Set(h) ++ t.content
      }

      // Verify
      def reverse: List[T] = {
        reverse0(Nil())
      } ensuring(_.content == this.content)

      def reverse0(acc: List[T]): List[T] = (this match {
        case Nil() => acc
        case Cons(h, t) => t.reverse0(Cons(h, acc))
      }) // TODO: Add appropriate post-condition


      def append(that: List[T]): List[T] = (this match {
        case Nil() => that
        case Cons(h, t) => Cons(h, t.append(that))
      }) ensuring(_.content == this.content ++ that.content)


    }
    case class Cons[T](head: T, tail: List[T]) extends List[T]
    case class Nil[T]() extends List[T]


    // Verify
    def sizesAreEquiv[T](l: List[T]): Boolean = {
      l.size == l.sizeTailRec
    }.holds


    def sizeAndContent[T](l: List[T]): Boolean = {
      l.size == 0 || l.content != Set[T]()
    }.holds

    def drunk[T](l: List[T]): List[T] = (l match {
      case Nil() => Nil[T]()
      case Cons(x,l1) => Cons(x,Cons(x,drunk(l1)))
    }) ensuring {
      res => true // TODO: find postcondition
    }


    def funnyCons[T](x: T, l: List[T]): List[T] = (l match {
        case Nil() => Cons(x, Nil())
        case c @ Cons(_,_) => Cons(x, c)
    }) ensuring(_.size > 0)


    @induct
    def nilAppend[T](l: List[T]): Boolean = {
      l.append(Nil()) == l
    }.holds

    @induct
    def appendAssoc[T](xs: List[T], ys: List[T], zs: List[T]) : Boolean = {
      false  // find predicate
    }.holds

    @induct
    def sizeAppend[T](l1: List[T], l2 : List[T]) : Boolean = {
      (l1.append(l2).size == l1.size + l2.size)
    }.holds
}
