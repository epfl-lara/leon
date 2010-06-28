import scala.collection.immutable.Set

object RedBlack {

  abstract sealed class Color;
  case class Red() extends Color;
  case class Black() extends Color;

  abstract sealed class Tree;
  case class EmptyTree() extends Tree;
  case class Node(color : Color, left: Tree, elem: Int, right: Tree) extends Tree;

  // Invariant 1. No red node has a red parent
  def invariant1(t: Tree): Boolean = t match {
    case EmptyTree() => true
    case Node(Black(), left, _, right) => invariant1(left) && invariant1(right)
    case Node(Red(), Node(Red(), _, _, _), _, _) => false
    case Node(Red(), _, _, Node(Red(), _, _, _)) => false
    case Node(Red(), left, _, right) => invariant1(left) && invariant1(right)
  }
  /// Invariant 1 END

  // Invariant 2. Each path from the root to an
  // empty node contains the same number of black
  // nodes
  
  def countBlackNodes(t: Tree): Int = t match {
    case EmptyTree() => 1
    case Node(Red(), left, _, _) => countBlackNodes(left)
    case Node(Black(), left, _, _) => countBlackNodes(left) + 1
  }

  def invariant2(t: Tree, n: Int): Boolean = t match {
    case EmptyTree() if n == 1 => true
    case EmptyTree() => false
    case Node(Red(), left, _, right) => invariant2(left, n) && invariant2(right, n)
    case Node(Black(), left, _, right) => invariant2(left, n-1) && invariant2(right, n-1)
  }

  /// Invariant 2 END

  def member(t: Tree, e: Int): Boolean = t match {
    case EmptyTree() => false
    case Node(_, _, x, _) if x == e => true
    case Node(_, left, x, _) if e < x => member( left, e)
    case Node(_, _, _, right) => member(right, e)
  }

  def contents(t: Tree): Set[Int] = t match {
    case EmptyTree() => Set.empty
    case Node(_, left, x, right) => contents(left) ++ contents(right) ++ Set(x)
  }

  def makeBlack(t: Tree) = {
    require(t != EmptyTree())
    //val Node(_, left, x, right) = t 
    //Node(Black(), left, x, right)
    t match {
      case Node(_, left, x, right) => Node(Black(), left, x, right)
    }
  } ensuring ((x:Tree) => x match {case Node(Black(), _, _, _) => true; case _ => false})

  def ins_(t: Tree, e: Int): Tree = t match {
    case EmptyTree() => Node(Red(), EmptyTree(), e, EmptyTree())
    case Node(color, left, x, right) if x < e => balance(Node(color, ins_(left, e), x, right))
    case Node(color, left, x, right) if x > e => balance(Node(color, left, x, ins_(right, e)))
    // Element already exists
    case t => t
  }

  def balance(t: Tree) : Tree =  {
    require(t != EmptyTree())
    t match {
      case Node(Black(), Node(Red(), Node(Red(), a, x, b), y, c), z, d) => Node(Red(), Node(Black(), a, x, b), y, Node(Black(), c, z, d))
      case Node(Black(), Node(Red(), a, x, Node(Red(), b, y, c)), z, d) => Node(Red(), Node(Black(), a, x, b), y, Node(Black(), c, z, d))
      case Node(Black(), a, x, Node(Red(), Node(Red(), b, y, c), z, d)) => Node(Red(), Node(Black(), a, x, b), y, Node(Black(), c, z, d))
      case Node(Black(), a, x, Node(Red(), b, y, Node(Red(), c, z, d))) => Node(Red(), Node(Black(), a, x, b), y, Node(Black(), c, z, d))
      case t => t
    }
  } ensuring (_ => true)

  def insert(t: Tree, e: Int): Tree = makeBlack( ins_(t, e) ) ensuring {res => invariant1(res) && invariant2(res, countBlackNodes(res))}

  def main(args : Array[String]) = {
    var rb : Tree = EmptyTree()
    for(ii <- 1 to 10) {
      rb = insert( rb, ii )
      println(rb)
    }
  }
}
  

