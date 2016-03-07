/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Subtyping1 {

  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree

  def content(t: Tree) : Set[Int] = t match {
    case Leaf() => Set.empty
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def treeMax(tree: Node): Int = {
    tree.right match {
      case Leaf() => tree.value
      case n:Node => treeMax(n)
    }
  } ensuring(content(tree).contains(_))

  def f2(tree: Node): Int = {
    require(treeMax(tree) > 0)
    tree.right match {
      case Leaf() => tree.value
      case n:Node => f2(n)
    }
  } ensuring(content(tree).contains(_))

}
