import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.collection._
import leon.lang.synthesis._

object Diffs {

  def diffs(l: List[BigInt]): List[BigInt] =
    /*
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
    */
    choose((res: List[BigInt]) => 
      res.size == l.size && undiff(res) == l
    )

  def undiff(l: List[BigInt]) = {
    l.scanLeft(BigInt(0))(_ + _).tail
  }
} 

