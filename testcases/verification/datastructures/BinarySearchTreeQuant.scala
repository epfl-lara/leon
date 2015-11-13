import leon.lang._
import leon.collection._

object BSTSimpler {
  case object Leaf extends Tree
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree
  sealed abstract class Tree {
    def isBST: Boolean = this match {
      case Leaf => true
      case Node(left, v, right) => {
        left.isBST && right.isBST &&
        forall((x:BigInt) => (left.content.contains(x) ==> x < v)) &&
        forall((x:BigInt) => (right.content.contains(x) ==> v < x))
      }
    }

    def content: Set[BigInt] = this match {
      case Leaf => Set.empty[BigInt]
      case Node(l, v, r) => l.content ++ Set(v) ++ r.content
    }

    def insert(value: BigInt): Node = {
      require(isBST)
      this match {
	case Leaf => Node(Leaf, value, Leaf)
	case Node(l, v, r) => (if (v < value) {
          Node(l, v, r.insert(value))
	} else if (v > value) {
          Node(l.insert(value), v, r)
	} else {
          Node(l, v, r)
	})
      }
    } ensuring(res => res.isBST && res.content == content ++ Set(value))

    def contains(value: BigInt): Boolean = {
      require(isBST)
      this match {
        case Leaf => false
        case Node(l,v,r) => (if (v < value) {
	  r.contains(value)
	} else if (v > value) {
          l.contains(value)
	} else true)
      }
    } ensuring(res => (res == content.contains(value)))

  }
  def empty: Tree = Leaf
}
