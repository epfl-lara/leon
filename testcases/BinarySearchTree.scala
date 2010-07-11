import scala.collection.immutable.Set

object BinarySearchTree {
  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def emptySet(): Tree = Leaf()

  sealed abstract class Option
  case class None() extends Option
  case class Some(value: Int) extends Option

  sealed abstract class Triple
  case class SortedTriple(min: Option, max: Option, sorted: Boolean) extends Triple

  /*
    def isSorted(tree: Tree): SortedTriple = tree match {
      case Leaf() => SortedTriple(None(), None(), true)
      case Node(l,v,r) => sorted(l) match {
        case SortedTriple(minl,maxl,false) => SortedTriple(None(), None(), false)
  case SortedTriple(minl, maxl, _) => minl match {
    case None() => maxl match {
      case None() =>  sorted(r) match {
        case SortedTriple(_,_,false) => SortedTriple(None(), None(), false)
        case SortedTriple(minr,maxr,_) => minr match {
          case None() => maxr match {
      case None() => SortedTriple(Some(v),Some(v),true)
      case _ => SortedTriple(None(),None(),false)
    }
    case Some(minrv) => maxr match {
      case Some(maxrv) => if (minrv > v) SortedTriple(Some(v),Some(maxrv),true) else SortedTriple(None(),None(),false)
      case _ => SortedTriple(None(),None(),false)
    }
        }
      }
      case _ => SortedTriple(None(),None(),false)
    }
    case Some(minlv) => maxl match {
      case Some(maxlv) => sorted(r) match {
        case SortedTriple(_,_,false) => SortedTriple(None(), None(), false)
        case SortedTriple(minr,maxr,_) => minr match {
          case None() => maxr match {
      case None() => if (maxlv <= v) SortedTriple(Some(minlv),Some(v),true) else SortedTriple(None(),None(),false)
      case _ => SortedTriple(None(),None(),false)
    }
    case Some(minrv) => maxr match {
      case Some(maxrv) => if (maxlv <= v && minrv > v) SortedTriple(Some(minlv),Some(maxrv),true) else SortedTriple(None(),None(),false)
      case _ => SortedTriple(None(),None(),false)
    }
        }
      }
      case _ => SortedTriple(None(),None(),false)
    }
  }
      }
    }
  */

  def treeMin(tree: Node): Int = tree match {
    case Node(left, v, _) => left match {
      case Leaf() => v
      case n@Node(_, _, _) => treeMin(n)
    }
  }

  def treeMax(tree: Node): Int = {
    // requires(isSorted(tree))
    tree match {
      case Node(_, v, right) => right match {
        case Leaf() => v
        case n@Node(_, _, _) => treeMax(n)
      }
    }
  } //ensuring (_ == contents(tree).max)

  def insert(tree: Tree, value: Int): Node = {
    //require(isSorted(tree))
    tree match {
      case Leaf() => Node(Leaf(), value, Leaf())
      case n@Node(l, v, r) => if (v < value) {
        Node(l, v, insert(r, value))
      } else if (v > value) {
        Node(insert(l, value), v, r)
      } else {
        n
      }
    }
  } ensuring (contents(_) == contents(tree) ++ Set(value))

  def dumbInsert(tree: Tree): Node = {
    tree match {
      case Leaf() => Node(Leaf(), 0, Leaf())
      case Node(l, e, r) => Node(dumbInsert(l), e, r)
    }
  } ensuring (contents(_) == contents(tree) ++ Set(0))

/*
    def remove(tree: Tree, value: Int) : Node = (tree match {
        case Leaf() => Node(Leaf(), value, Leaf())
        case n @ Node(l, v, r) => if(v < value) {
          Node(l, v, insert(r, value))
        } else if(v > value) {
          Node(insert(l, value), v, r)
        } else {
          n
        }
    }) ensuring (contents(_) == contents(tree) -- Set(value))
*/

  def dumbInsertWithOrder(tree: Tree): Node = {
    tree match {
      case Leaf() => Node(Leaf(), 0, Leaf())
      case Node(l, e, r) => Node(dumbInsert(l), e, r)
    }
  } ensuring (res => {val S = contents(res); S == contents(tree) ++ Set(0) && S.min <= 0 && S.max >= 0})


  def createRoot(v: Int): Node = {
    Node(Leaf(), v, Leaf())
  } ensuring (contents(_) == Set(v))

  /*
      def remove(tree: Tree, value: Int) : Node = (tree match {
          case Leaf() => Node(Leaf(), value, Leaf())
          case n @ Node(l, v, r) => if(v < value) {
            Node(l, v, insert(r, value))
          } else if(v > value) {
            Node(insert(l, value), v, r)
          } else {
            n
          }
      }) ensuring (contents(_) == contents(tree) -- Set(value))
  */

  def mkInfiniteTree(x: Int): Node = {
    Node(mkInfiniteTree(x), x, mkInfiniteTree(x))
  } ensuring (res =>
    res.left != Leaf() && res.right != Leaf()
  )

  def contains(tree: Tree, value: Int): Boolean = tree match {
    case Leaf() => false
    case n@Node(l, v, r) => if (v < value) {
      contains(r, value)
    } else if (v > value) {
      contains(l, value)
    } else {
      true
    }
  }

  def contents(tree: Tree): Set[Int] = tree match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => contents(l) ++ Set(v) ++ contents(r)
  }
}

