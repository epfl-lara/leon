import cp.Definitions._
import cp.Constraints._
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
}

object RedBlackTree {
  import Specs._

  def main(args: Array[String]) : Unit = {
    val defaultBound = 3
    val bound = if (args.isEmpty) defaultBound else args(0).toInt

    // enumerateAllUpTo(bound)

    val solutionSet = scala.collection.mutable.Set[Tree]()
    println("Fixing size of trees to " + (bound))
    for (tree <- ((t : Tree) => isRedBlackTree(t) && valuesWithin(t, bound - 1) && size(t) == bound).findAll) {
      solutionSet += tree
    }

    // for (tree <- solutionSet)
    //   println(print(tree) + "\n-----------\n")
    println("Fixed-size solution set size : " + solutionSet.size)
    Stopwatch.printSummary
  }

  def enumerateAllUpTo(bound : Int) : Unit = {
    println("Bound is " + bound)

    val set1 = scala.collection.mutable.Set[Tree]()
    val set2 = scala.collection.mutable.Set[Tree]()
    val set3 = scala.collection.mutable.Set[Tree]()
    val set4 = scala.collection.mutable.Set[Tree]()

    println("Minimizing size:")
    for (tree <- (((t : Tree) => isRedBlackTree(t) && valuesWithin(t, bound)) minimizing ((t: Tree) => size(t))).findAll) {
      set1 += tree
    }
    
    /*
    println("Minimizing height:")
    for (tree <- findAll((t : Tree) => isRedBlackTree(t) && valuesWithin(t, bound) minimizing height(t))) {
      set2 += tree
    }

    println("Minimizing bound:")
    for ((tree, bb) <- findAll((t : Tree, b: Int) => isRedBlackTree(t) && valuesWithin(t, b) && b >= 0 && b <= bound minimizing b)) {
      set3 += tree
    }
    
    println("No minimization:")
    for (tree <- findAll((t : Tree) => isRedBlackTree(t) && valuesWithin(t, bound))) {
      set4 += tree
    }

    assert(set1 == set2)
    assert(set1 == set3)
    assert(set1 == set4)
    */
    println("Solution set size: " + set1.size)
  }

  /** Printing trees */
  def indent(s: String) = ("  "+s).split('\n').mkString("\n  ")

  def print(tree: Tree): String = tree match {
    case Node(c,l,v,r) =>
      indent(print(r)) + "\n" + (if (c == Black()) "B" else "R") + " " + v.toString + "\n" + indent(print(l))
    case Empty() => "E"
  }
}
