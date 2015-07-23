import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Numerals {
  sealed abstract class Num
  case object Z extends Num
  case class  S(pred: Num) extends Num

  def value(n: Num): BigInt = {
    n match {
      case Z => BigInt(0)
      case S(p) => 1 + value(p)
    }
  } ensuring (_ >= 0)

  def add(x: Num, y: Num): Num = {
    choose { (r: Num) =>
      value(r) == value(x) + value(y)
    }
  }
}
