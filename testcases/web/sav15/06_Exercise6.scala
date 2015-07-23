import leon.lang._
import leon.collection._
import leon._
/**
 * 1) Implement the isSearchTree property that checks bounds of elements in a
 *    search tree. Assume that the tree is strictly sorted (no dupplicates)
 *
 * 2) Implement operations on Binary Search Trees as efficiently as you can.
 *    These operations will likely not verify, but make sure that leon does not
 *    find counter-examples within a reasonnable timeout (e.g. --timeout=5 )
 *
 *    You do not need to change the pre-/post-conditions
 *
 * 3) Implement toList to return a sorted list from a search tree.
 */

object BinaryTree {

  abstract class Tree {
    def content: Set[BigInt] = {
      this match {
        case Empty => Set()
        case Node(l, v, r) => l.content ++ Set(v) ++ r.content
      }
    }

    def size: BigInt = {
      this match {
        case Empty => BigInt(0)
        case Node(l, _, r) => l.size + r.size + 1
      }
    } ensuring { _ >= 0 }


    def +(x: BigInt): Tree = {
      require(isBT)
      this // TODO
    } ensuring {
      res => res.isBT &&
             res.content == this.content ++ Set(x) &&
             res.size >= this.size &&
             res.size <= this.size + 1
    }

    def -(x: BigInt): Tree = {
      require(isBT)
      this // TODO
    } ensuring {
      res => res.isBT &&
             res.content == this.content -- Set(x) &&
             res.size <= this.size &&
             res.size >= this.size - 1
    }

    def ++(that: Tree): Tree = {
      require(this.isBT && that.isBT)
      this // TODO
    } ensuring {
      res => res.isBT && res.content == this.content ++ that.content
    }

    def contains(x: BigInt): Boolean = {
      require(isBT)
      false // TODO
    } ensuring {
      res => res == (content contains x)
    }

    def toList: List[BigInt] = {
      require(isBT)
      Nil[BigInt]() // TODO
    } ensuring {
      res => res.content == this.content && isSorted(res)
    }

    // Properties

    def isBT: Boolean = {
      isSearchTree(None(), None())
    }

    def isSearchTree(min: Option[BigInt], max: Option[BigInt]): Boolean = {
      this match {
        case Empty => true
        case Node(l, v, r) =>
          true // TODO
      }
    }
  }

  case object Empty extends Tree
  case class Node(l: Tree, v: BigInt, r: Tree) extends Tree


  def isSorted(l: List[BigInt]): Boolean = {
    l match {
      case Cons(v1, t @ Cons(v2, _)) if v1 >= v2 => false
      case Cons(h, t) => isSorted(t)
      case Nil() => true
    }
  }
}


