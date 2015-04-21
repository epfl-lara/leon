import leon.lang._
import leon.collection._
import annotation._

object RedBlackTree { 
  sealed abstract class Color
  case object Red extends Color
  case object Black extends Color
 
  sealed abstract class Tree {
    /* We consider leaves to be black by definition */
    def color = this match {
      case Empty => Black
      case Node(c,_,_,_) => c
    }

    def content : Set[Int] = this match {
      case Empty => Set.empty
      case Node(_, l, v, r) => l.content ++ Set(v) ++ r.content
    }

    def size : Int = this match {
      case Empty => 0
      case Node(_, l, v, r) => l.size + 1 + r.size
    }

    def isBlack = color == Black

    def blackHeight : Int = this match {
      case Empty => 1
      case Node(Black, l, _, _) => l.blackHeight + 1
      case Node(Red, l, _, _) => l.blackHeight
    }

    def max : Option[Int] = this match {
      case Empty => None()
      case Node(_, l, v, r) => 
        maxOption(Some(v), maxOption(l.max, r.max))
    }

    def min : Option[Int] = this match {
      case Empty => None()
      case Node(_, l, v, r) => 
        minOption(Some(v), minOption(l.max, r.max)) 
    }

  }
  
  def minOption(i1 : Option[Int], i2 : Option[Int]) : Option[Int] = (i1, i2) match {
    case (Some(i1), Some(i2)) => Some(if (i1 < i2) i1 else i2)
    case _ => i1 orElse i2
  }
   
  def maxOption(i1 : Option[Int], i2 : Option[Int]) : Option[Int] = (i1, i2) match {
    case (Some(i1), Some(i2)) => Some(if (i1 > i2) i1 else i2)
    case _ => i1 orElse i2
  }

  case object Empty extends Tree
  case class Node(color_ : Color, left: Tree, value: Int, right: Tree) extends Tree
  
  def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty => true
    case Node(Black, l, _, r) =>
      redNodesHaveBlackChildren(l) &&
      redNodesHaveBlackChildren(r)
    case Node(Red, l, _, r) =>
      l.isBlack && r.isBlack &&
      redNodesHaveBlackChildren(l) &&
      redNodesHaveBlackChildren(r)
  }

  def redDescHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty => true
    case Node(_,l,_,r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && l.blackHeight == r.blackHeight
    case Empty => true
  }
  
  def keysSorted(t : Tree) : Boolean = t match {
    case Empty => true
    case Node(_, l, v, r) =>
      keysSorted(l) && keysSorted(r) && 
      (l.max.getOrElse (v-1) < v) && 
      (r.min.getOrElse (v+1) > v)
  }


  // <<insert element x into the tree t>>
  def ins(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t) && keysSorted(t))
    val newT = t match {
      case Empty => Node(Red,Empty,x,Empty)
      case n@Node(c,a,y,b) =>
        if      (x < y)  Node(c, ins(x, a), y, b)
        else if (x == y) n
        else             Node(c, a, y, ins(x, b))
    }  
    newT match {
      case Node(Black,Node(Red,Node(Red,a,xV,b),yV,c),zV,d) => 
        Node(Red,Node(Black,a,xV,b),yV,Node(Black,c,zV,d))
      case Node(Black,Node(Red,a,xV,Node(Red,b,yV,c)),zV,d) => 
        Node(Red,Node(Black,a,xV,b),yV,Node(Black,c,xV,d)) // FIXME: second xV -> zV
      case Node(Black,a,xV,Node(Red,Node(Red,b,yV,c),zV,d)) => 
        Node(Red,Node(Black,a,xV,b),yV,Node(Black,c,zV,d))
      case Node(Black,a,xV,Node(Red,b,yV,Node(Red,c,zV,d))) => 
        Node(Red,Node(Black,a,xV,b),yV,Node(Black,c,zV,d))
      case other => other 
    }
  } ensuring (res => 
    res.content == t.content ++ Set(x) &&
    t.size <= res.size &&
    res.size <= t.size + 1 &&
    keysSorted(res) &&
    redDescHaveBlackChildren(res) && 
    blackBalanced(res) 
  )

  def makeBlack(n: Tree): Tree = {
    require(
      redDescHaveBlackChildren(n) &&
      blackBalanced(n) &&
      keysSorted(n)
    )
    n match {
      case Node(Red,l,v,r) => Node(Black,l,v,r)
      case _ => n
    }
  } ensuring { res =>
    res.isBlack &&
    redNodesHaveBlackChildren(res) && 
    blackBalanced(res) && 
    keysSorted(res)
  }

  def add(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t) && keysSorted(t))
    makeBlack(ins(x, t))
  } ensuring { res => 
    res.content == t.content ++ Set(x) && 
    redNodesHaveBlackChildren(res) && 
    blackBalanced(res) &&
    keysSorted(res)
  }
  
}
