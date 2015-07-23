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

  def add(x: Num, y: Num): Num = (x match {
    case Z => y
    case S(p) => add(p, S(y))
  }) ensuring (value(_) == value(x) + value(y))

  def distinct(x: Num, y: Num): Num = {
    choose { (r : Num) =>
      r != x && r != y
    }
  }
}
