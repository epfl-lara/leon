import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._
import leon.grammar.Grammar._

object StrictSortedListInsert {

  def size(l: List[BigInt]): BigInt = (l match {
    case Nil() => BigInt(0)
    case Cons(_, t) => BigInt(1) + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List[BigInt]): Set[BigInt] = l match {
    case Nil() => Set.empty[BigInt]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x1, t@Cons(x2, _)) =>
      x1 < x2 && isSorted(t)
    case _ => true
  }

  def insert(in1: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(in1))
    // Solution:
    /*in1 match {
      case Nil() => Cons(v, Nil())
      case Cons(h,t) =>
        if (v > h) Cons(h, insert(t, v))
        else if (v == h) in1
        else Cons(v, Cons(h, t))
    }*/
    ???[List[BigInt]]
  } ensuring { (out : List[BigInt]) =>
    /*((in1, v), out) passes {
      case (Cons(BigInt(1), Cons(BigInt(2), Nil())), BigInt(0)) =>
        Cons(BigInt(0), Cons(BigInt(1), Cons(BigInt(2), Nil())))
      case (Cons(BigInt(1), Cons(BigInt(2), Nil())), BigInt(1)) =>
        Cons(BigInt(1), Cons(BigInt(2), Nil()))
      case (Cons(BigInt(1), Cons(BigInt(2), Nil())), BigInt(2)) =>
        Cons(BigInt(1), Cons(BigInt(2), Nil()))
      case (Cons(BigInt(1), Cons(BigInt(2), Nil())), BigInt(3)) =>
        Cons(BigInt(1), Cons(BigInt(2), Cons(BigInt(3), Nil())))
    }*/
    (content(out) == content(in1) ++ Set(v)) && isSorted(out)
  }
  
}
