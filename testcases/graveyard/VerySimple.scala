import scala.collection.immutable.Set
import leon.lang._
import leon.annotation._

object VerySimple {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(_ >= 0)

    def content(l: List) : Set[Int] = l match {
      case Nil() => Set.empty[Int]
      case Cons(x, xs) => Set(x) ++ content(xs)
    }

    def sizeAndContent(l: List) : Boolean = {
      size(l) == 0 || content(l) != Set.empty[Int]
    } holds

    sealed abstract class IntPairList
    case class IPCons(head: IntPair, tail: IntPairList) extends IntPairList
    case class IPNil() extends IntPairList

    sealed abstract class IntPair
    case class IP(fst: Int, snd: Int) extends IntPair

    def iplSize(l: IntPairList) : Int = (l match {
      case IPNil() => 0
      case IPCons(_, xs) => 1 + iplSize(xs)
    }) ensuring(_ >= 0)

    def zip(l1: List, l2: List) : IntPairList = {
      // try to comment this and see how pattern-matching becomes
      // non-exhaustive and post-condition fails
      require(size(l1) == size(l2))

      l1 match {
        case Nil() => IPNil()
        case Cons(x, xs) => l2 match {
          case Cons(y, ys) => IPCons(IP(x, y), zip(xs, ys))
        }
      }
    } ensuring(iplSize(_) == size(l1))

    def usesPrec(l1: List, l2: List, l3: List, flag: Boolean) : IntPairList = {
      require(size(l1) == size(l2))

      if(flag) {
        zip(l1, l2)
      } else {
        zip(l2, l3)
      }
    }
}
