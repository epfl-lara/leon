import scala.collection.immutable.Set

object ParseMe {
  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def inside(n: Node): Int = getIt().value

  def getIt() : Node = Node(Leaf(), 12, Leaf())

  def insert(v: Int, t: Tree): Tree = t match {
    case Leaf() if v == 5 => Leaf()
    case Leaf() => Node(Leaf(), v, Leaf())
    case Node(Leaf(), 12, Leaf()) => Leaf()
    case _ => Leaf()
  }

  def emptySet() : Tree = {
    Leaf()
  }

  def withIf(a: Int) : Int = { if(a < 0) -a else if(a > 0) a+1 else a-1 } ensuring (_ > 17)
}
