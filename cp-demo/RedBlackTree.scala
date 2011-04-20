import cp.Definitions._

object RedBlackTree { 
  @spec sealed abstract class Color
  @spec case class Red() extends Color
  @spec case class Black() extends Color
 
  @spec sealed abstract class Tree
  @spec case class Empty() extends Tree
  @spec case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  @spec sealed abstract class OptionInt
  @spec case class Some(v : Int) extends OptionInt
  @spec case class None() extends OptionInt

  @spec def max(a: Int, b: Int) : Int = {
    if (a >= b) a else b
  } ensuring (res => res >= a && res >= b)

  @spec def size(t: Tree) : Int = (t match {
    case Empty() => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }) ensuring (_ >= 0)

  @spec def height(t: Tree) : Int = (t match {
    case Empty() => 0
    case Node(_,l,_,r) => max(height(l), height(r)) + 1
  }) ensuring (_ >= 0)

  @spec def isBlack(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(),_,_,_) => true
    case _ => false
  }

  @spec def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  @spec def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }

  @spec def blackHeight(t : Tree) : Int = t match {
    case Empty() => 1
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
  }

  @spec def boundValues(t : Tree, bound : Int) : Boolean = t match {
    case Empty() => true
    case Node(_,l,v,r) => 0 <= v && v <= bound && boundValues(l,bound) && boundValues(r,bound)
  }

  @spec def orderedKeys(t : Tree) : Boolean = orderedKeys(t, None(), None())

  @spec def orderedKeys(t : Tree, min : OptionInt, max : OptionInt) : Boolean = t match {
    case Empty() => true
    case Node(c,a,v,b) =>
      val minOK = 
        min match {
          case Some(minVal) =>
            v > minVal
          case None() => true
        }
      val maxOK =
        max match {
          case Some(maxVal) =>
            v < maxVal
          case None() => true
        }
      minOK && maxOK && orderedKeys(a, min, Some(v)) && orderedKeys(b, Some(v), max)
  }

  @spec def isRedBlackTree(t : Tree) : Boolean = {
    blackBalanced(t) && redNodesHaveBlackChildren(t) && orderedKeys(t) // && isBlack(t)
  }

  def enumerateAllUpTo(bound : Int) : Unit = {
    println("Bound is " + bound)

    val set1 = scala.collection.mutable.Set[Tree]()
    val set2 = scala.collection.mutable.Set[Tree]()
    val set3 = scala.collection.mutable.Set[Tree]()
    val set4 = scala.collection.mutable.Set[Tree]()

    println("Minimizing size:")
    Timer.go
    for (tree <- findAll((t : Tree) => isRedBlackTree(t) && boundValues(t, bound) minimizing size(t))) {
      set1 += tree
    }
    Timer.stop
    
    println("Minimizing height:")
    Timer.go
    for (tree <- findAll((t : Tree) => isRedBlackTree(t) && boundValues(t, bound) minimizing height(t))) {
      set2 += tree
    }
    Timer.stop

    println("Minimizing bound:")
    Timer.go
    for ((tree, bb) <- findAll((t : Tree, b: Int) => isRedBlackTree(t) && boundValues(t, b) && b >= 0 && b <= bound minimizing b)) {
      set3 += tree
    }
    Timer.stop
    
    println("No minimization:")
    Timer.go
    for (tree <- findAll((t : Tree) => isRedBlackTree(t) && boundValues(t, bound))) {
      set4 += tree
    }
    Timer.stop

    println("Solution set size: " + set1.size)
    assert(set1 == set2)
    assert(set1 == set3)
    assert(set1 == set4)
  }

  def main(args: Array[String]) : Unit = {
    val defaultBound = 3
    val bound = if (args.isEmpty) defaultBound else args(0).toInt

    enumerateAllUpTo(bound)

    val solutionSet = scala.collection.mutable.Set[Tree]()
    println("Fixing size of trees to " + (bound))
    Timer.go
    for (tree <- findAll((t : Tree) => isRedBlackTree(t) && boundValues(t, bound - 1) && size(t) == bound)) {
      solutionSet += tree
    }
    Timer.stop
    
    // for (tree <- solutionSet)
    //   println(print(tree) + "\n#####\n")
    println("Fixed-size solution set size : " + solutionSet.size)
  }

  /** Printing trees */
  def indent(s: String) = ("  "+s).split('\n').mkString("\n  ")

  def print(tree: Tree): String = tree match {
    case Node(c,l,v,r) =>
      indent(print(r)) + "\n" + (if (c == Black()) "B" else "R") + " " + v.toString + "\n" + indent(print(l))
    case Empty() => "E"
  }
}

object Timer {
  var start: Long = 0L
  var end: Long = 0L
  def go = {
    start = System.currentTimeMillis
  }
  def stop : Double = {
    end = System.currentTimeMillis
    val seconds = (end - start) / 1000.0
    println("  Measured time: " + seconds + " s")
    seconds
  }
}
