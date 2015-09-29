import leon.invariant._
import leon.instrumentation._
import scala.collection.immutable.Set

object RedBlackTree {
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color

  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: BigInt, right: Tree) extends Tree

  def twopower(x: BigInt) : BigInt = {
    require(x >= 0)
    if(x < 1) 1
    else
      2* twopower(x - 1)
  }

  def size(t: Tree): BigInt = {
    require(blackBalanced(t))
    (t match {
      case Empty() => BigInt(0)
      case Node(_, l, v, r) => size(l) + 1 + size(r)
    })
  } ensuring (res => tmpl((a,b) => twopower(blackHeight(t)) <= a*res + b))

  def blackHeight(t : Tree) : BigInt = {
   t match {
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
    case _ => 0
   	}
  }

   //We consider leaves to be black by definition
  def isBlack(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(),_,_,_) => true
    case _ => false
  }

  def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case _ => false
  }

  def redDescHaveBlackChildren(t: Tree) : Boolean = t match {
    case Node(_,l,_,r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case _ => true
  }

  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case _ => true
  }

  // <<insert element x BigInto the tree t>>
  def ins(x: BigInt, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))

    t match {
      case Empty() => Node(Red(),Empty(),x,Empty())
      case Node(c,a,y,b) =>
        if(x < y) {
        	val t1 = ins(x, a)
        	balance(c, t1, y, b)
        }
        else if (x == y){
        	Node(c,a,y,b)
        }
        else{
          val t1 = ins(x, b)
          balance(c,a,y,t1)
        }
    }
  } ensuring(res => tmpl((a,b) => stack <= a*blackHeight(t) + b))

  def makeBlack(n: Tree): Tree = {
    n match {
      case Node(Red(),l,v,r) => Node(Black(),l,v,r)
      case _ => n
    }
  }

  def add(x: BigInt, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t) )
    val t1 =  ins(x, t)
    makeBlack(t1)

  } ensuring(res => tmpl((a,b) => stack <= a*blackHeight(t) + b))

  def balance(co: Color, l: Tree, x: BigInt, r: Tree): Tree = {
    Node(co,l,x,r)
     match {
      case Node(Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) =>
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) =>
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) =>
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) =>
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case _ => Node(co,l,x,r)
    }
  }
}
