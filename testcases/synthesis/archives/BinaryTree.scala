import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object BinaryTree {
  sealed abstract class Tree
  case class Node(left : Tree, value : Int, right : Tree) extends Tree
  case class Leaf() extends Tree

  def content(t : Tree): Set[Int] = t match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def delete(in : Tree, v : Int) = choose { (out : Tree) =>
    content(out) == (content(in) -- Set(v))
  }

  def deleteSubProblem(left : Tree, leftR: Tree, value: Int, rightRleft: Tree, rightRvalue: Int, rightRright: Tree, rightR: Tree, right: Tree, toRemove : Int) = choose { (out : Tree) =>
    content(out) == (content(Node(left, value, right)) -- Set(toRemove)) && content(leftR) == (content(left) -- Set(toRemove)) && rightR == Node(rightRleft, rightRvalue, rightRright) && content(Node(rightRleft, rightRvalue, rightRright)) == (content(right) -- Set(toRemove)) && value == toRemove
  }

  def deleteSubProblem2(left : Tree, leftR: Tree, value: Int, rightRleft: Tree, rightRvalue: Int, rightRright: Tree, right: Tree, toRemove : Int) = choose { (out : Tree) =>
    content(out) == (content(Node(left, value, right)) -- Set(toRemove)) && content(leftR) == (content(left) -- Set(toRemove)) && content(Node(rightRleft, rightRvalue, rightRright)) == (content(right) -- Set(toRemove)) && value == toRemove
  }
}
