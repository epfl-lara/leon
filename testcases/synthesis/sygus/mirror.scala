import leon._
import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object Mirror {

  def inttuple(a: BigInt, b: BigInt): (BigInt, BigInt) = {
    ???[(BigInt, BigInt)]
  } ensuring {
    out => out._1+1 == a && out._2-1 == b
  }

  def tuple(a: List[BigInt], b: List[BigInt]): (List[BigInt], List[BigInt]) = {
    ???[(List[BigInt], List[BigInt])]
  } ensuring {
    out => out._1 == a && out._2 == b
  }

  def mirror1(a: List[BigInt], b: List[BigInt]): (List[BigInt], List[BigInt]) = {
    ???[(List[BigInt], List[BigInt])]
  } ensuring {
    out => out._1 == b && out._2 == a
  }

  def mirror2[T](a: List[T], b: List[T]): (List[T], List[T]) = {
    ???[(List[T], List[T])]
  } ensuring {
    out => out._1 == b && out._2 == a
  }

  def transfer(a: List[BigInt], b: List[BigInt]): (List[BigInt], List[BigInt]) = {
    ???[(List[BigInt], List[BigInt])]
  } ensuring {
    out =>
      (a, b) match {
        case (Cons(ah, at), b) => (out._2.head == (ah + 1)) && (out._2.tail == b)
        case _ => true
      }
  }

}
