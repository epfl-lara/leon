object Account {
  case class Acc(checking : Int, savings : Int)

  def toSavings(x : Int, a : Acc) : Acc = {
    require (x > 0)
    a match { case Acc(c0,s0) => Acc(c0 - x, s0 + x) }
  } ensuring (_ => true)
}
