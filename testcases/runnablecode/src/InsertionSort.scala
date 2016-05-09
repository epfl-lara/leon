import leon.invariant._
import leon.instrumentation._

object InsertionSort {
  abstract class List
  
  case class Cons(head : BigInt, tail : List) extends List
  
  case class Nil() extends List
  
  def size(l : List): BigInt = l match {
    case Cons(_, xs) =>
      BigInt(1) + size(xs)
    case _ =>
      BigInt(0)
  }
  
  def sortedInstimedepth(e : BigInt, l : List): (List, BigInt, BigInt) = {
    val bd = l match {
      case Cons(x, xs) =>
        val c11 = BigInt(1)
        val expr = if (x <= e) {
          val e19 = sortedInstimedepth(e, xs)
          (Cons(x, e19._1), BigInt(4) + e19._2, {
            val mt = BigInt(2) + e19._3
            if (c11 >= mt) {
              c11
            } else {
              mt
            }
          })
        } else {
          (Cons(e, l), BigInt(3), if (BigInt(1) >= c11) {
            BigInt(1)
          } else {
            c11
          })
        }
        (expr._1, BigInt(4) + expr._2, BigInt(1) + expr._3)
      case _ =>
        (Cons(e, Nil()), BigInt(4), BigInt(3))
    }
    (bd._1, bd._2, bd._3)
  }
  
  def sorttimerec(l : List): (List, BigInt, BigInt) = {
    val bd1 = l match {
      case Cons(x, xs) =>
        val e30 = sorttimerec(xs)
        val e28 = sortedInstimedepth(x, e30._1)
        (e28._1, (BigInt(6) + e28._2) + e30._2, BigInt(1) + e30._3)
      case _ =>
        (Nil(), BigInt(3), BigInt(0))
    }
    (bd1._1, bd1._2, bd1._3)
  }

  def main(args: Array[String]): Unit = {
  }
}
