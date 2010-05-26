import scala.collection.immutable.Set

object ParseMe {
  sealed abstract class Tree
  //case class Node(value: Int) extends Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def getSet(s: Int): Tree = {
    if (4 + s < 2 + s && s > 4) {
      emptySet()
    } else {
      Node(Leaf(), 1, Leaf())
    }
  }

  def emptySet() : Tree = {
    Leaf()
  }
}
