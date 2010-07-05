object Account {
  sealed abstract class AccLike 
  case class Acc(checking : Int, savings : Int) extends AccLike

  def sameTotal(a1 : Acc, a2 : Acc) : Boolean = {
    a1.checking + a1.savings == a2.checking + a2.savings
  }

  def toSavings(x : Int, a : Acc) : Acc = {
    require (x >= 0 && a.checking >= x)
    Acc(a.checking - x, a.savings + x)
  } ensuring (res => (res.checking >= 0 && sameTotal(a, res)))
}
