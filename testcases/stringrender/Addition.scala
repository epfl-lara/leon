import scala.language.postfixOps
import leon.lang._
import leon.proof.check
import leon.annotation._
import synthesis._

object Addition {
  
  abstract class DigitList
  case class ZeroZero(tail: DigitList) extends DigitList
  case class OneZero(tail: DigitList) extends DigitList
  case class ZeroOne(tail: DigitList) extends DigitList
  case class OneOne(tail: DigitList) extends DigitList
  case class Nil() extends DigitList
  
  def listPairToString(in : DigitList): String =  {
    choose((hole$111 : String) => (in, hole$111) passes {
      case OneOne(OneOne(Nil())) =>
        "011"
      case ZeroZero(ZeroZero(Nil())) =>
        "00"
      case ZeroOne(Nil()) =>
        "1"
      case OneZero(Nil()) =>
        "1"
      case OneZero(OneOne(Nil())) =>
        "101"
      case ZeroOne(OneOne(Nil())) =>
        "101"
      case ZeroZero(OneOne(Nil())) =>
        "001"
    })
  } ensuring {
    (hole$230 : String) => (in, hole$230) passes {
      case OneOne(OneOne(Nil())) =>
        "011"
      case ZeroZero(ZeroZero(Nil())) =>
        "00"
      case ZeroOne(Nil()) =>
        "1"
      case OneZero(Nil()) =>
        "1"
      case OneZero(OneOne(Nil())) =>
        "101"
      case ZeroOne(OneOne(Nil())) =>
        "101"
      case ZeroZero(OneOne(Nil())) =>
        "001"
    }
  }
}
