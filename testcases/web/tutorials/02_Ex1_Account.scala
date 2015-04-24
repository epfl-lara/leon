/*
  Try to verify the toSavings function.
  Use the returned counter-example to fix the precondition such that
  Leon succeeds in showing the function correct.
*/

object Account2 {
  sealed abstract class AccLike
  case class Acc(checking : BigInt, savings : BigInt) extends AccLike

  def toSavings(x : BigInt, a : Acc) : Acc = {
    require (notRed(a) && a.checking >= x)
    Acc(a.checking - x, a.savings + x)
  } ensuring (res => (notRed(res) && sameTotal(a, res)))


  def sameTotal(a1 : Acc, a2 : Acc) : Boolean = {
    a1.checking + a1.savings == a2.checking + a2.savings
  }
  def notRed(a : Acc) : Boolean = {
    a.checking >= 0 && a.savings >= 0
  }
}
