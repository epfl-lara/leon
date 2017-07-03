import leon.lang._
import leon.collection._

object Diffs {

  def diffs(l: List[BigInt]): List[BigInt] =
    l match {
      case Nil() =>
        List[BigInt]()
      case Cons(h, t) =>
        diffs(t) match {
          case Nil() =>
            Cons[BigInt](h, t)
          case Cons(h$1, t$1) =>
            Cons[BigInt](h, Cons[BigInt](h$1 - h, t$1))
        }
    }

  def undiff(l: List[BigInt]) = {
    l.scanLeft(BigInt(0))(_ + _).tail
  }
} 

