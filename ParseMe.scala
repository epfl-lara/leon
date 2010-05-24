import scala.collection.immutable.Set

object ParseMe {
  sealed abstract class Tree
  //case class Node(value: Int) extends Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def fromSet(i: Set[Set[Boolean]]) : Int = {
    5
  }
}
