import leon.lang._
import leon.lang.synthesis._

object ChurchNumerals {
  sealed abstract class Num
  case class Zero() extends Num
  case class Succ(pred:Num) extends Num

  def value(n:Num) : Int = {
    n match {
      case Zero() => 0
      case Succ(p) => 1 + value(p)
    }
  } ensuring (_ >= 0)

  def succ(n:Num) : Num = Succ(n) ensuring(value(_) == value(n) + 1)

  def add(x:Num, y:Num):Num = {
    choose { (r : Num) => 
      value(r) == value(x) + value(y)
    }
  }

  def workingAdd(x : Num, y : Num) : Num = (x match {
    case Zero() => y
    case Succ(p) => workingAdd(p, Succ(y))
  }) ensuring (value(_) == value(x) + value(y))
}
