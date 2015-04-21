import leon.lang._
import leon.collection._

object BSTSimpler {
  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def size(t : Tree) : Int = (t match {
    case Leaf() => 1
    case Node(l,_,r) => size(l) + 1 + size(r)
  }) ensuring(_ >= 1)

  sealed abstract class IntOpt
  case class Some(value: Int) extends IntOpt
  case class None() extends IntOpt

  sealed abstract class TripleAbs
  case class Triple(lmax: IntOpt, isSorted: Boolean, rmin: IntOpt) extends TripleAbs

  sealed abstract class TriplePairAbs
  case class TriplePair(left: TripleAbs, right: TripleAbs) extends TriplePairAbs

  def isBST(tree: Tree) : Boolean = isBST0(tree) match {
    case Triple(_, v, _) => v
  }

  def isBST0(tree: Tree) : TripleAbs = tree match {
    case Leaf() => Triple(None(), true, None())

    case Node(l, v, r) => TriplePair(isBST0(l), isBST0(r)) match {
      case TriplePair(Triple(None(),t1,None()),Triple(None(),t2,None()))
        if(t1 && t2) =>
          Triple(Some(v),true,Some(v))
      case TriplePair(Triple(Some(minL),t1,Some(maxL)),Triple(None(),t2,None()))
        if(t1 && t2 && minL <= maxL && maxL < v) =>
          Triple(Some(minL),true,Some(v))
      case TriplePair(Triple(None(),t1,None()),Triple(Some(minR),t2,Some(maxR)))
        if(t1 && t2 && minR <= maxR && v < minR) =>
          Triple(Some(v),true,Some(maxR))
      case TriplePair(Triple(Some(minL),t1,Some(maxL)),Triple(Some(minR),t2,Some(maxR)))
        if(t1 && t2 && minL <= maxL && minR <= maxR && maxL < v && v < minR) =>
          Triple(Some(minL),true,Some(maxR))

      case _ => Triple(None(),false,None())
    }
  }

  def emptySet(): Tree = Leaf()

  def insert(tree: Tree, value: Int): Node = {
    require(isBST(tree))
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
  } ensuring(res => isBST(res) && content(res) == content(tree) ++ Set(value))

/*
  def remove(tree : Tree, value : Int) : Tree = {
    require(size(tree) <= 1 && isBST(tree))
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
  }
*/

  def createRoot(v: Int): Node = {
    Node(Leaf(), v, Leaf())
  } ensuring (content(_) == Set(v))

  def content(tree: Tree): Set[Int] = tree match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
  }
}

