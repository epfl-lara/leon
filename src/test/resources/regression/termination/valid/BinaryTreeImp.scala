/* Copyright 2009-2014 EPFL, Lausanne */

import scala.collection.immutable.Set
import leon.annotation._
import leon.lang._

object BinaryTree { 
 
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree

  sealed abstract class OptionInt
  case class Some(v : Int) extends OptionInt
  case class None() extends OptionInt

  def content(t: Tree) : Set[Int] = t match {
    case Leaf() => Set.empty
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def size(t: Tree) : Int = (t match {
    case Leaf() => 0
    case Node(l, v, r) => size(l) + 1 + size(r)
  }) ensuring(_ >= 0)

  def binaryTreeProp(t: Tree): Boolean = t match {
    case Leaf() => true
    case Node(left, value, right) => {
      val b1 = left match {
        case Leaf() => true
        case Node(a,b,c) => value >= treeMax(Node(a,b,c))
      }
      val b2 = right match {
        case Leaf() => true
        case Node(a,b,c) => value <= treeMin(Node(a,b,c))
      }
      binaryTreeProp(left) && binaryTreeProp(right) && b1 && b2
    }
  }

  def treeMin(tree: Node): Int = {
    require(binaryTreeProp(tree))
    tree match {
      case Node(left, value, _) => left match {
        case Leaf() => value
        case Node(l, v, r) => treeMin(Node(l, v, r))
      }
    }
  } ensuring(content(tree).contains(_))

  //def treeMin(tree: Node): Int = {
  //  require(binaryTreeProp(tree))
  //  val Node(left, value, _) = tree
  //  var res = value
  //  var tmpLeft = left
  //  (while(!tmpLeft.isInstanceOf[Leaf]) {
  //    val Node(left, value, _) = tmpLeft
  //    res = value
  //    tmpLeft = left
  //  }) invariant(content(tmpLeft).contains(res))
  //  res
  //} ensuring(content(tree).contains(_))

  def treeMax(tree: Node): Int = {
    require(binaryTreeProp(tree))
    tree match {
      case Node(_, v, right) => right match {
        case Leaf() => v
        case Node(l, v, r) => treeMax(Node(l, v, r))
      }
    }
  } ensuring(content(tree).contains(_))


  def search(t: Tree, x: Int): Boolean = {
    require(binaryTreeProp(t))
    t match {
      case Leaf() => false
      case Node(left, value, right) =>
        if(value == x) true
        else if(value < x) search(right, x)
        else search(left, x)
    }
  } ensuring(res => res == content(t).contains(x))
  
  def searchImp(t: Tree, x: Int): Boolean = {
    require(binaryTreeProp(t))
    var res = false
    var t2: Tree = t
    (while(!t2.isInstanceOf[Leaf]) {
      val Node(left, value, right) = t2
      if(value == x)
        res = true
      else if(value < x) 
        t2 = right
      else
        t2 = left
    })
    res
  } ensuring(res => res == content(t).contains(x))

}
