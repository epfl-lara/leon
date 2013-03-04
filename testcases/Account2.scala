object Account2 {
  sealed abstract class AccLike 
  case class Acc(checking : Int, savings : Int) extends AccLike

  def sameTotal(a1 : Acc, a2 : Acc) : Boolean = {
    a1.checking + a1.savings == a2.checking + a2.savings
  }
  def notRed(a : Acc) : Boolean = {
    a.checking >= 0 && a.savings >= 0
  }

  def toSavingsOk(x : Int, a : Acc) : Acc = {
    require (notRed(a) && x >= 0 && a.checking >= x)
    Acc(a.checking - x, a.savings + x)
  } ensuring (res => (notRed(res) && sameTotal(a, res)))

  def toSavingsBroken(x : Int, a : Acc) : Acc = {
    require (notRed(a) && a.checking >= x)
    Acc(a.checking - x, a.savings + x)
  } ensuring (res => (notRed(res) && sameTotal(a, res)))

}
