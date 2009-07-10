import funcheck.lib.Specs._

object BSTTest {
  /** Specification Variables */
  def content(t : BST) : Set[Int] = t match {
    case Leaf() => Set.empty
    case Node(left,right,v) => (content(left) ++ Set(v) ++ content(right))
  }
  
  def contains(key: Int, t : BST): Boolean = { 
    t match {
      case Leaf() => false
      case Node(left,right,v) => {
	if (key == v) true
	else if (key < v) contains(key, left)
	else contains(key, right)
      }
      }
  }
  
  /** Properties */
  forAll[(BST,Int)]( p => contains(p._2,p._1) == content(p._1).contains(p._2))
  
  /** Program */
  @generator
  sealed abstract class BST
  case class Node(left: BST, right: BST, v: Int) extends BST
  case class Leaf() extends BST 
}
