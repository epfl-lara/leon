import cp.Definitions._
import cp.Annotations._

object FindAllCalls { 
  @pure sealed abstract class Color
  @pure case class Red() extends Color
  @pure case class Black() extends Color
 
  @pure sealed abstract class Tree
  @pure case class Empty() extends Tree
  @pure case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  @pure def size(t: Tree) : Int = t match {
    case Empty() => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }

  @pure def isBlack(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(),_,_,_) => true
    case _ => false
  }

  @pure def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  @pure def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }

  @pure def blackHeight(t : Tree) : Int = t match {
    case Empty() => 1
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
  }

  @pure def property(t : Tree) : Boolean = {
    isBlack(t) && blackBalanced(t) && redNodesHaveBlackChildren(t)
  }

  def main(args: Array[String]) : Unit = {

    /** Printing trees */
    def indent(s: String) = ("  "+s).split('\n').mkString("\n  ")

    def print(tree: Tree): String = tree match {
      case Node(c,l,v,r) =>
        indent(print(r)) + "\n" + (if (c == Black()) "B" else "R") + " " + v.toString + "\n" + indent(print(l))
      case Empty() => "E"
    }

    for (tree <- findAll((t : Tree) => property(t) && size(t) == 5)) {
      println("Here is a tree: ")
      println(print(tree))
    }
  }
}
