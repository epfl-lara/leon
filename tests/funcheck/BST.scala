package funcheck

import funcheck.lib.Specs._

object BST extends Application {
  /** class hierarchy*/
  sealed abstract class BST
  @generator case class Empty() extends BST
  case class Node(left: BST, value: Int, right: BST) extends BST

  /** used for specification purposes */
  def content(t : BST) : Set[Int] = t match {
    case Empty() => Set.empty
    case Node(left,v,right) => (content(left) ++ Set(v) ++ content(right))
  }

  /** compute the size of the given tree*/
  def size(t : BST) : Int = t match {
    case Empty() => 0
    case Node(left,v,right) => size(left) + 1 + size(right)
  }

  /** build correct binary trees (this should be used instead of the default 
   * case class constructor) */
  @generator 
  def add(x : Int, t : BST) : Node = {
    t match {
      case Empty() => Node(Empty(),x,Empty())
      case t @ Node(left,v,right) => {
	    if (x < v) Node(add(x, left), v, right)
	    else if (x==v) t
	    else Node(left, v, add(x, right))
      }
    }
  } 

  /** check if the tree contains the key */
  def contains(key: Int, t : BST): Boolean = { 
    t match {
      case Empty() => false
      case Node(left,v,right) => {
	    if (key == v) true
	    else if (key < v) contains(key, left)
	    else contains(key, right)
      }
    }
  } 

  /** global assertions */
  forAll[(BST,Int)]( p => contains(p._2,p._1) == content(p._1).contains(p._2))
  forAll[(BST,Int)]( p => content(add(p._2, p._1)) == content(p._1) + p._2)
  
}

