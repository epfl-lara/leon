import scala.collection.immutable.Set
//import scala.collection.immutable.Multiset

object BSTSimpler {
  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def emptySet(): Tree = Leaf()

  def insert(tree: Tree, value: Int): Node = {
    tree match {
      case Leaf() => Node(Leaf(), value, Leaf())
      case Node(l, v, r) => (if (v < value) {
        Node(l, v, insert(r, value))
      } else if (v > value) {
        Node(insert(l, value), v, r)
      } else {
        Node(l, v, r)
      })
    }
  } ensuring (contents(_) == contents(tree) ++ Set(value))

  def dumbInsert(tree: Tree): Node = {
    tree match {
      case Leaf() => Node(Leaf(), 0, Leaf())
      case Node(l, e, r) => Node(dumbInsert(l), e, r)
    }
  } ensuring (contents(_) == contents(tree) ++ Set(0))

  def createRoot(v: Int): Node = {
    Node(Leaf(), v, Leaf())
  } ensuring (contents(_) == Set(v))

  def contents(tree: Tree): Set[Int] = tree match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => contents(l) ++ Set(v) ++ contents(r)
  }
}

