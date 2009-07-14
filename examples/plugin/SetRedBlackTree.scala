package plugin

import funcheck.lib.Specs._

/*** Okasaki-style red-black tree maps. ***/

// Based on:
// http://www.eecs.usma.edu/webs/people/okasaki/jfp99.ps

object SetRedBlackTree {
  @generator
  sealed abstract class Color
  case class Red() extends Color // Red.
  case class Black() extends Color // Black.
  
  
  sealed abstract class Tree
  @generator case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree
  
  
  def member(x: Int, t:Tree): Boolean = t match {
    case Empty() => false
    case Node(_,a,y,b) => 
      if (x < y) member(x,a)
      else if (x > y) member(x,b)
      else true
  }
  
  @generator
  def insert(x: Int, t: Tree): Tree = {
    def ins(t: Tree): Tree = t match {
      case Empty() => Node(Red(),Empty(),x,Empty())
      case Node(c,a,y,b) =>
        if      (x < y)  balance(c, ins(a), y, b)
        else if (x == y) Node(c,a,y,b)
        else             balance(c,a,y,ins(b))
    }
    makeBlack(ins(t))
  }
  
  def balance(c: Color, a: Tree, x: Int, b: Tree): Tree = (c,a,x,b) match {
    case (Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) => 
      Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
    case (Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) => 
      Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
    case (Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) => 
      Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
    case (Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) => 
      Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
    case (c,a,xV,b) => Node(c,a,xV,b)  
  }
  
  /** makeBlack: Turn a node black. */
  def makeBlack(n: Tree): Tree = n match {
    case Node(Red(),l,v,r) => Node(Black(),l,v,r)
    case _ => n
  }
  
  /* global invariants: 
   * Red-black trees are binary search trees obeying two key invariants:
   *
   * (1) Any path from a root node to a leaf node contains the same number
   *     of black nodes. (A balancing condition.)
   *
   * (2) Red nodes always have black children.
   *
   */
  forAll{t: Tree => anyPathsContainsSameNumberOfBlackNodes(t)} //(1)
  forAll{t: Tree => areRedNodeChildrenBlack(t)} //(2)
  
  
  /* Empty tree are considered to be black */
  def isBlack(t: Tree): Boolean = t match {
    case Node(Red(),_,_,_) => false
    case _ => true
  }
  
  
  def anyPathsContainsSameNumberOfBlackNodes(t: Tree): Boolean = {
    def blacks(t: Tree, acc: Int): List[Int] = t match {
      case Empty() => List(acc + 1) // because Empty are assumed to be black
      case n @ Node(_,l,_,r) => 
        val upAcc = if(isBlack(t)) acc + 1 else acc 
        blacks(l,upAcc) ::: blacks(r,upAcc)  
    }
    val paths = blacks(t, 0)
    
    if(paths.isEmpty)
      true
    else
      paths.forall(_ == paths.head)
  } 
  
  def areRedNodeChildrenBlack(t: Tree): Boolean = t match {
    case Node(Red(),l,_,r) =>
      isBlack(l) && isBlack(r) &&
      areRedNodeChildrenBlack(l) && areRedNodeChildrenBlack(r)
    case Node(Black(),l,_,r) =>
      areRedNodeChildrenBlack(l) && areRedNodeChildrenBlack(r)
    case _ => true
  }
  
  def main(args: Array[String]) = {}
}

