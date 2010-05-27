import scala.collection.immutable.Set

object ParseMe {
  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree



  def insert(v: Int, t: Tree): Tree = t match {
    case Leaf() => Node(Leaf(), v, Leaf())
    case Node(left, v2, right) if v2 > v => Node(insert(v, left), v2, right)
    case Node(left, v2, right) if v2 < v => Node(left, v2, insert(v, right))
    case n @ Node(left, v2, right) if v2 == v => n
  }

  def emptySet() : Tree = {
    Leaf()
  }

}
