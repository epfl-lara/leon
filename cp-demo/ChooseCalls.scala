import cp.Definitions._

object Specs { 
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
}

object ChooseCalls {

  import Specs._

  private val random = new scala.util.Random()
  def randomInt() : Int = random.nextInt(10)

  def chooseTree(height : Int) : Tree = {
    val outer = height
    choose((anInt: Int, t: Tree) => blackBalanced(t) && redNodesHaveBlackChildren(t) && isBlack(t) && size(t) == randomInt())._2
  }

  /** Printing trees */
  def indent(s: String) = ("  "+s).split('\n').mkString("\n  ")

  def print(tree: Tree): String = tree match {
    case Node(c,l,v,r) =>
      indent(print(r)) + "\n" + (if (c == Black()) "B" else "R") + " " + v.toString + "\n" + indent(print(l))
    case Empty() => "E"
  }

  def main(args: Array[String]) : Unit = {


    val height = if (args.isEmpty) 3 else args(0).toInt
    println("The chosen tree is : \n" + print(chooseTree(height)))

    /*
    println("Invoke choose on unsat. constraint: ")
    try {
      choose((t : Tree) => size(t) > 5 && size(t) < 4)
    } catch {
      case e : UnsatisfiableConstraintException => println("I caught an exception as expected.")
    }

    println("Invoke `find' on unsat. constraint: " )
    find((t: Tree) => size(t) > 5 && size(t) < 4) match {
      case None => println("Result is None, as expected.")
      case _    => println("Whoops?")
    }

    println(choose((x : Int, y : Int, w : Int) => 
      w == 3*x + 2*y && 
      2*x + y >= 6 && 
      x + y >= 4 &&
      x >= 0 &&
      y >= 0 minimizing (w + height))
    )

    println(choose((x : Int, y : Int, z : Int) =>
      z == 4*x + 6*y &&
      y - x <= 11 &&
      x + y <= 27 &&
      2*x + 5*y <= 90 &&
      x >= 0 &&
      y >= 0 maximizing z)
    )
   
    */

  }
}
