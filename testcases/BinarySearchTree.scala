import scala.collection.immutable.Set

object BinarySearchTree {
    sealed abstract class Tree
    case class Node(left: Tree, value: Int, right: Tree) extends Tree
    case class Leaf() extends Tree

    def emptySet() : Tree = Leaf()

    def insert(tree: Tree, value: Int) : Node = (tree match {
        case Leaf() => Node(Leaf(), value, Leaf())
        case n @ Node(l, v, r) => if(v < value) {
          Node(l, v, insert(r, value))
        } else if(v > value) {
          Node(insert(l, value), v, r)
        } else {
          n
        }
    }) ensuring(_ != Leaf()) //ensuring(result => contents(result) != Set.empty[Int])

    def contains(tree: Tree, value: Int) : Boolean = tree match {
        case Leaf() => false
        case Node(_, v, _) if v == value => true 
        case Node(l, v, r) if v < value => contains(r, value)
        case Node(l, v, r) if v > value => contains(l, value)
    }

    def contents(tree: Tree) : Set[Int] = tree match {
        case Leaf() => Set.empty[Int]
        case Node(l, v, r) => contents(l) ++ Set(v) ++ contents(r)
    }
}

