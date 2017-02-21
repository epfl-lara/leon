import leon.lang._
import leon.lang.synthesis._
import leon.grammar.Grammar._
import leon.grammar._
import leon.annotation.grammar._

object UnaryNumeralsAdd {

  @production(1)
  def z: Num = Z
  @production(1)
  def s(pred: Num): Num = S(pred)
  @production(1)
  def v: Num = variable[Num]

  sealed abstract class Num
  case object Z extends Num
  case class  S(pred: Num) extends Num

  def value(n: Num): BigInt = {
    n match {
      case Z => BigInt(0)
      case S(p) => BigInt(1) + value(p)
    }
  } ensuring (_ >= 0)

  def add(x: Num, y: Num): Num = {
    choose { (r : Num) =>
      value(r) == value(x) + value(y)
    }
  }
}
