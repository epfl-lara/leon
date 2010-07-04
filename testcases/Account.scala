object Account {
  sealed abstract class AccLike 
  case class Acc(checking : Int, savings : Int) extends AccLike

  def toSavings(x : Int, a : Acc) : Acc = {
    require (a.checking > x)
    Acc(a.checking - x, a.savings + x)
    // a match { case Acc(c0,s0) => Acc(c0 - x, s0 + x) }
  } ensuring (_.checking >= 0)
}
