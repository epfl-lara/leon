import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object BinaryTree {
  sealed abstract class Tree
  case class Node(left : Tree, value : Int, right : Tree) extends Tree
  case object Leaf extends Tree

  def content(t : Tree): Set[Int] = t match {
    case Leaf => Set()
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def size(t: Tree): Int = {
    t match {
      case Leaf => 0
      case Node(l, v, r) => size(l) + size(r) + 1
    }
  } ensuring { _ >= 0 }

  def insert(in: Tree, v: Int): Tree = {
    Node(in, v, Leaf)
  } ensuring { res => content(res) == content(in) ++ Set(v) }

  def delete(in: Tree, v: Int): Tree = {
    in match {
      case Node(l, vv, r) =>
        if (vv == v) {
          delete(l, v) match {
            case Node(ll, lv, lr) =>
              Node(Node(ll, lv, lr), lv, delete(r, v))
            case Leaf =>
              delete(r, v)
          }
        } else {
          Node(delete(l, v), vv, delete(r, v))
        }
      case Leaf =>
        Leaf
    }
  } ensuring { res => content(res) == content(in) -- Set(v) }

  // def union(in1: Tree, in2: Tree): Tree = {
  //   in1 match {
  //     case Node(l1, v1, r1) =>
  //       insert(union(r1, union(l1, in2)), v1)
  //     case Leaf =>
  //       in2
  //   }
  // } ensuring { res => content(res) == content(in1) ++ content(in2) }

  def union(in1: Tree, in2: Tree): Tree = choose {
    (res: Tree) => content(res) == content(in1) ++ content(in2)
  }
}
