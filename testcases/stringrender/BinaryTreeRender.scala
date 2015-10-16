/** 
  * Name:     BinaryTreeRender.scala
  * Creation: 14.10.2015
  * Author:   Mika�l Mayer (mikael.mayer@epfl.ch)
  * Comments: Binary tree rendering specifications.
  */

import leon.lang._
import string.String
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object TreeRender {
  sealed abstract class Tree[T]
  case class Node[T](left: Node[T], i: T, right: Node[T]) extends Tree[T]
  case class Leaf[T]() extends Tree[T]
  
  /** Synthesis by example specs */
  @inline def psStandard(s: Tree[Int])(res: String) = (s, res) passes {
    case Node(Node(Leaf(), 2, Leaf()), 1, Node(Leaf(), -3, Leaf())) => "Node(Node(Leaf(), 2, Leaf()), 1, Node(Leaf(), -3, Leaf()))"
    case Node(Leaf(), 1, Leaf()) => "Node(Leaf(), 1, Leaf())"
    case Leaf() => "Leaf()"
  }
  
  @inline def psRemoveNode(s: Tree[Int])(res: String) = (s, res) passes {
    case Node(Node(Leaf(), 2, Leaf()), 1, Node(Leaf(), -3, Leaf())) => "((Leaf(), 2, Leaf()), 1, (Leaf(), -3, Leaf()))"
    case Node(Leaf(), 1, Leaf()) => "(Leaf(), 1, Leaf())"
    case Leaf() => "Leaf()"
  }
  
  @inline def psRemoveLeaf(s: Tree[Int])(res: String) = (s, res) passes {
    case Node(Node(Leaf(), 2, Leaf()), 1, Node(Leaf(), -3, Leaf())) => "((, 2, ), 1, (, -3, ))"
    case Node(Leaf(), 1, Leaf()) => "(, 1, )"
    case Leaf() => ""
  }
  
  @inline def psRemoveComma(s: Tree[Int])(res: String) = (s, res) passes {
    case Node(Node(Leaf(), 2, Leaf()), 1, Node(Leaf(), -3, Leaf())) => "((2), 1, (-3))"
    case Node(Leaf(), 1, Node(Leaf(), 2, Leaf())) => "(1, (2))"
    case Node(Node(Leaf(), 2, Leaf()), 1, Leaf()) => "((2), 1)"
    case Leaf() => ""
  }
  
  @inline def psRemoveParentheses(s: Tree[Int])(res: String) = (s, res) passes {
    case Node(Node(Leaf(), 2, Leaf()), 1, Node(Leaf(), -3, Leaf())) => "(2), 1, (-3)"
    case Node(Leaf(), 1, Node(Leaf(), 2, Leaf())) => "1, (2)"
    case Node(Node(Leaf(), 2, Leaf()), 1, Leaf()) => "(2), 1"
    case Leaf() => ""
  }
  
  @inline def psPrefix(s: Tree[Int])(res: String) = (s, res) passes {
    case Node(Node(Leaf(), 2, Leaf()), 1, Node(Leaf(), -3, Leaf())) => "1 (2) (-3)"
    case Node(Leaf(), 1, Node(Leaf(), 2, Leaf())) => "1 () (2)"
    case Node(Node(Leaf(), 2, Leaf()), 1, Leaf()) => "1 (2) ()"
    case Leaf() => "()"
  }
  
  @inline def psLispLike(s: Tree[Int])(res: String) = (s, res) passes {
    case Node(Node(Leaf(), 2, Leaf()), 1, Node(Leaf(), -3, Leaf())) => "(1 (2) (-3))"
    case Node(Leaf(), 1, Node(Leaf(), 2, Leaf())) => "(1 () (2))"
    case Node(Node(Leaf(), 2, Leaf()), 1, Leaf()) => "(1 (2) ())"
    case Leaf() => "()"
  }
  
  @inline def psSuffix(s: Tree[Int])(res: String) = (s, res) passes {
    case Node(Node(Leaf(), 2, Leaf()), 1, Node(Leaf(), -3, Leaf())) => "(2) (-3) 1"
    case Node(Leaf(), 1, Node(Leaf(), 2, Leaf())) => "() (2) 1"
    case Node(Node(Leaf(), 2, Leaf()), 1, Leaf()) => "(2) () 1"
    case Leaf() => "()"
  }
  
  //////////////////////////////////////////////
  // Non-incremental examples: pure synthesis //
  //////////////////////////////////////////////
  def synthesizeStandard(s: List[Int]): String = {
    ???[String]
  } ensuring psStandard(s)

  def synthesizeRemoveNode(s: List[Int]): String = {
    ???[String]
  } ensuring psRemoveNode(s)
  
  def synthesizeRemoveLeaf(s: List[Int]): String = {
    ???[String]
  } ensuring psRemoveLeaf(s)
  
  def synthesizeRemoveComma(s: List[Int]): String = {
    ???[String]
  } ensuring psRemoveComma(s)
  
  def synthesizeRemoveParentheses(s: List[Int]): String = {
    ???[String]
  } ensuring psRemoveParentheses(s)
  
  def synthesizePrefix(s: List[Int]): String = {
    ???[String]
  } ensuring psPrefix(s)
  
  def synthesizeLispLike(s: List[Int]): String = {
    ???[String]
  } ensuring psLispLike(s)
  
  def synthesizeSuffix(s: List[Int]): String = {
    ???[String]
  } ensuring psSuffix(s)
}