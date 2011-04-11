import cp.Definitions._

object ChooseCalls { 
  @spec sealed abstract class Color
  @spec case class Red() extends Color
  @spec case class Black() extends Color

  @spec sealed abstract class Tree
  @spec case class Empty() extends Tree
  @spec case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  @spec
  def size(t: Tree) : Int = t match {
    case Empty() => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }

  @spec
  def isBlack(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(),_,_,_) => true
    case _ => false
  }

  @spec
  def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  @spec
  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }

  @spec
  def blackHeight(t : Tree) : Int = t match {
    case Empty() => 1
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
  }

  private val random = new scala.util.Random()
  def randomInt() : Int = random.nextInt(10)

  def plus2(i : Int) : Int = i + 2

  def sizePlus2(t : Tree) : Int = size(t) + 2

  def chooseTree(height : Int) : Tree = {
    val outer = height
    choose((anInt: Int, t: Tree) => blackBalanced(t) && redNodesHaveBlackChildren(t) && isBlack(t) && size(t) == randomInt())._2
  }

  def main(args: Array[String]) : Unit = {

    /** Printing trees */
    def indent(s: String) = ("  "+s).split('\n').mkString("\n  ")

    def print(tree: Tree): String = tree match {
      case Node(c,l,v,r) =>
        indent(print(r)) + "\n" + (if (c == Black()) "B" else "R") + " " + v.toString + "\n" + indent(print(l))
      case Empty() => "E"
    }

    val height = if (args.isEmpty) 3 else args(0).toInt
    println("The chosen tree (of height " + height + ") is : \n" + print(chooseTree(height)))
  }
}
