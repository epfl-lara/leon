import scala.collection.immutable.Set
import funcheck.Annotations._
import funcheck.Utils._

import cp.Definitions._
import cp.Terms._
import purescala.Stopwatch

@spec object Specs { 
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color
 
  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  sealed abstract class OptionInt
  case class SomeInt(v : Int) extends OptionInt
  case class NoneInt() extends OptionInt

  def content(t: Tree) : Set[Int] = t match {
    case Empty() => Set.empty
    case Node(_, l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def max(a: Int, b: Int) : Int = {
    if (a >= b) a else b
  } ensuring (res => res >= a && res >= b)

  def size(t: Tree) : Int = (t match {
    case Empty() => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }) ensuring (_ >= 0)

  def height(t: Tree) : Int = (t match {
    case Empty() => 0
    case Node(_,l,_,r) => max(height(l), height(r)) + 1
  }) ensuring (_ >= 0)

  def isBlack(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(),_,_,_) => true
    case _ => false
  }

  def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def redDescHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(_,l,_,r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }

  def blackHeight(t : Tree) : Int = t match {
    case Empty() => 0
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
  }

  def valuesWithin(t : Tree, bound : Int) : Boolean = t match {
    case Empty() => true
    case Node(_,l,v,r) => 0 <= v && v <= bound && valuesWithin(l,bound) && valuesWithin(r,bound)
  }

  def orderedKeys(t : Tree) : Boolean = orderedKeys(t, NoneInt(), NoneInt())

  def orderedKeys(t : Tree, min : OptionInt, max : OptionInt) : Boolean = t match {
    case Empty() => true
    case Node(c,a,v,b) =>
      val minOK = 
        min match {
          case SomeInt(minVal) =>
            v > minVal
          case NoneInt() => true
        }
      val maxOK =
        max match {
          case SomeInt(maxVal) =>
            v < maxVal
          case NoneInt() => true
        }
      minOK && maxOK && orderedKeys(a, min, SomeInt(v)) && orderedKeys(b, SomeInt(v), max)
  }

  def isRedBlackTree(t : Tree) : Boolean = {
    blackBalanced(t) && redNodesHaveBlackChildren(t) && orderedKeys(t) // && isBlack(t)
  }
  
  // <<insert element x into the tree t>>
  def ins(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
    t match {
      case Empty() => Node(Red(),Empty(),x,Empty())
      case Node(c,a,y,b) =>
        if      (x < y)  balance(c, ins(x, a), y, b)
        else if (x == y) Node(c,a,y,b)
        else             balance(c,a,y,ins(x, b))
    }
  } ensuring (res => content(res) == content(t) ++ Set(x) 
                   && size(t) <= size(res) && size(res) <= size(t) + 1
                   && redDescHaveBlackChildren(res)
                   && blackBalanced(res))

  def makeBlack(n: Tree): Tree = {
    require(redDescHaveBlackChildren(n) && blackBalanced(n))
    n match {
      case Node(Red(),l,v,r) => Node(Black(),l,v,r)
      case _ => n
    }
  } ensuring(res => redNodesHaveBlackChildren(res) && blackBalanced(res))

  def add(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
    makeBlack(ins(x, t))
  } ensuring (res => content(res) == content(t) ++ Set(x) && redNodesHaveBlackChildren(res) && blackBalanced(res))
  
  def balance(c: Color, a: Tree, x: Int, b: Tree): Tree = {
    Node(c,a,x,b) match {
      case Node(Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(c,a,xV,b) => Node(c,a,xV,b)
    }
  } ensuring (res => content(res) == content(Node(c,a,x,b)))// && redDescHaveBlackChildren(res))
}

object RedBlackTreeMethods {
  import Specs._

  def addDeclarative(x : Int, tree : Tree) : Tree =
    ((t : Tree) => isRedBlackTree(t) && content(t) == content(tree) ++ Set(x)).solve

  def removeDeclarative(x : Int, tree : Tree) : Tree =
    ((t : Tree) => isRedBlackTree(t) && content(t) == content(tree) -- Set(x)).solve

  def main(args: Array[String]) : Unit = {
    val defaultBound = 3
    val bound = if (args.isEmpty) defaultBound else args(0).toInt
    val nbTrees = if (args.size == 2) args(1).toInt else 5

    val tree = ((t : Tree) => isRedBlackTree(t) && size(t) == bound).solve

    val someTrees = for (i <- 1 to nbTrees) yield ((t : Tree) => isRedBlackTree(t) && size(t) == bound).solve

    println("Initial trees:")
    println(someTrees.map(treeString(_)).mkString("\n---------\n"))

    val treesWith42 = someTrees.map(addDeclarative(42, _))
    println("New trees with added element:")
    println(treesWith42.map(treeString(_)).mkString("\n---------\n"))

    val treesWithout42 = treesWith42.map(removeDeclarative(42, _))
    println("New trees with removed element:")
    println(treesWithout42.map(treeString(_)).mkString("\n---------\n"))

    Stopwatch.printSummary
  }

  /** Printing trees */
  def indent(s: String) = ("  "+s).split('\n').mkString("\n  ")

  def treeString(tree: Tree): String = tree match {
    case Node(c,l,v,r) =>
      indent(treeString(r)) + "\n" + (if (c == Black()) "B" else "R") + " " + v.toString + "\n" + indent(treeString(l))
    case Empty() => "E"
  }
}
