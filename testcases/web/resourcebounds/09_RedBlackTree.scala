import leon.invariant._
import leon.instrumentation._
import scala.collection.immutable.Set
import leon.lang._

object RedBlackTree {
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color

  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: BigInt, right: Tree) extends Tree

  def twopower(x: BigInt) : BigInt = {
    require(x >= 0)
    if(x <= 0) BigInt(1)
    else
      2* twopower(x - 1)
  } ensuring(_ >= 1)

  // uses integer division and equivalent to floor(log(x))
  def log(x: BigInt): BigInt = {
    require(x >= 1)
    if (x <= 1) BigInt(0)
    else 1 + log(x/2)
  } ensuring(_ >= 0)

  def logMonotone(x: BigInt, y: BigInt): Boolean = {
    require(x >= y && y >= 1)
    (if(y <= 1) true else logMonotone(x/2, y/2))  && 
      (log(x) >= log(y)) 
  } holds

  /**
  * Proof of the axiom: log(2^x) = x
  **/
  def logTwopowerAxiom(x: BigInt): Boolean =  {
    require(x >= 0)
    (if(x <= 0) true
    else logTwopowerAxiom(x - 1)) && log(twopower(x)) == x
  } holds  
  

  def size(t: Tree): BigInt = {
    require(blackBalanced(t))
    (t match {
      case Empty() => BigInt(0)
      case Node(_, l, v, r) => size(l) + 1 + size(r)
    })
  } ensuring (res => twopower(blackHeight(t)) <= res + 1)

  /**
  * Proof of the property that "blackHeight(t) <= log(size(t)+1)"
  **/
  def sizeBlackheightProp(t: Tree): Boolean = {
    require(blackBalanced(t))
    val bh = blackHeight(t)
    val sz =  size(t)+1
    logTwopowerAxiom(bh) &&
      logMonotone(sz, twopower(bh)) && 
      bh <= log(sz)
  } holds

  def blackHeight(t : Tree) : BigInt = {
   t match {
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
    case _ => BigInt(0)
   	}
  } ensuring(_ >= 0)

   //We consider leaves to be black
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
  
  def insRec(x: BigInt, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))

    t match {
      case Empty() => Node(Red(),Empty(),x,Empty())
      case Node(c,a,y,b) =>
        if(x < y) {
        	val t1 = insRec(x, a)
        	balance(c, t1, y, b)
        }
        else if (x == y){
        	Node(c,a,y,b)
        }
        else{
          val t1 = insRec(x, b)
          balance(c,a,y,t1)
        }
    }
  } ensuring(res => steps <= ? * blackHeight(t) + ?)

  def makeBlack(n: Tree): Tree = {
    n match {
      case Node(Red(),l,v,r) => Node(Black(),l,v,r)
      case _ => n
    }
  }

  // <<insert element x BigInto the tree t>>
  def ins(x: BigInt, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t) && 
      sizeBlackheightProp(t)) // this is an axiom instantiation and is always true 

    val t1 =  insRec(x, t)
    makeBlack(t1)

  } ensuring(res =>  steps <= ? * log(size(t)+1) + ?)

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
