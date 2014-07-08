/* Copyright 2009-2013 EPFL, Lausanne 
 *
 * Author: Manos (modified by Ravi)
 * Date: 20.11.2013
 **/

import leon._
import leon.lang._
import leon.annotation._ 

object AVLTree  {
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left : Tree, value : Int, right: Tree) extends Tree

  sealed abstract class OptionInt
  case class None() extends OptionInt
  case class Some(i:Int) extends OptionInt


  def smallerOption(o1:OptionInt,o2:OptionInt) : Boolean  = {
    (o1,o2) match {
      case (Some(i1), Some(i2)) => i1 < i2
      case (_,_) => true
    }
  }

  def minOption(o1:OptionInt,o2:OptionInt) : OptionInt = (
    (o1,o2) match {
      case (Some(i1), Some(i2)) => Some(if (i1<=i2) i1 else i2)
      case (Some(_), _) => o1
      case (_, Some(_)) => o2
      case _ => None()
    }
  )
  
  def maxOption(o1:OptionInt,o2:OptionInt) : OptionInt = (
    (o1,o2) match {
      case (Some(i1), Some(i2)) => Some(if (i1>=i2) i1 else i2)
      case (Some(_), _) => o1
      case (_, Some(_)) => o2
      case _ => None()
    }
  )

  def min(i1:Int, i2:Int) : Int = if (i1<=i2) i1 else i2
  def max(i1:Int, i2:Int) : Int = if (i1>=i2) i1 else i2

  private def size(t: Tree): Int = {
    (t match {
      case Leaf() => 0
      case Node(l, _, r) => size(l) + 1 + size(r)
    })
  } ensuring (_ >= 0)
 
  // O(n)
  @forceMemo
  def height(t: Tree): Int = {
    t match {
      case Leaf() => 0
      case Node(l, x, r) => {
        val hl = height(l)
        val hr = height(r)
        if (hl > hr) hl + 1 else hr + 1
      }
    }
  } ensuring(_ >= 0)

  def treeMax(t:Tree) : OptionInt = {
    t match {
      case Leaf()      => None()
      case Node(l,v,r) => maxOption(Some(v), maxOption (treeMax(l), treeMax(r)))
    }
  }

  def treeMin(t:Tree) : OptionInt = {
    t match {
      case Leaf()      => None()
      case Node(l,v,r) => minOption(Some(v), minOption (treeMin(l), treeMin(r)))
    }
  }

  // O(nlogn) assuming balanced
  def content(t : Tree) : Set[Int] = t match {
    case Leaf() => Set.empty[Int]
    case Node(l,v,r) => content(l) ++ Set[Int](v) ++ content(r)
  }

  def isBST(t:Tree) : Boolean = {
    t match {
      case Leaf() => true
      case Node(l,v,r) => 
        if (isBST(l) && isBST(r)) {
          smallerOption(Some(v),bstMin(r)) && 
          smallerOption(bstMax(l),Some(v))
        }
        else false 
    }
  }

  // O(n)
  def balanceFactor(t : Tree) : Int = {
    t match{
      case Leaf() => 0
      case Node(l, _, r) => height(l) - height(r)
    }
  } 
  
  // O(nlogn) assuming balanced trees
  def isAVL(t:Tree) : Boolean = {    
    t match {
        case Leaf() => true        
        case Node(l,v,r) =>  
          isAVL(l) && isAVL(r) && 
          smallerOption(treeMax(l),Some(v)) && smallerOption(Some(v),treeMin(r)) &&
          balanceFactor(t) >= -1 && balanceFactor(t) <= 1 
      }    
  } 

  def bstMax(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None() 
      case Node(_,v,Leaf()) => Some(v) 
      case Node(_,_,r)      => bstMax(r)
    }
  } ensuring (res => res == treeMax(t))

  def bstMin(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None()
      case Node(Leaf(),v,_) => Some(v) 
      case Node(l,     _,_) => bstMin(l)
    }
  } ensuring (res => res == treeMin(t))
  
  // O(nlogn)
  def offByOne(t : Tree) : Boolean = {
    t match {
      case Leaf() => true
      case Node(l,v,r) => 
        isAVL(l) && isAVL(r) && 
        balanceFactor(t) >= -2 && balanceFactor(t) <= 2 &&
        smallerOption(treeMax(l),Some(v)) && smallerOption(Some(v),treeMin(r)) 
    }
  }

  // T1(n) = O(nlogn) + T2(n/2)  
  // O(nlogn)
  @induct
  def unbalancedInsert(t: Tree, e : Int) : Tree = {
    require(isAVL(t))
    t match {
      case Leaf() => Node(Leaf(), e, Leaf())
      case Node(l,v,r) => 
             if (e == v) t
        else if (e <  v){
          val newl = avlInsert(l,e)
          Node(newl, v, r)
        } 
        else {
          val newr = avlInsert(r,e)
          Node(l, v, newr)
        }            
    }
  } ensuring(res => offByOne(res) && content(res) == content(t) ++ Set[Int](e))
             
  // T2(n) = O(nlogn) + T1(n) 
  // O(nlogn)
  def avlInsert(t: Tree, e : Int) : Tree = {    
    require(isAVL(t))
    
    balance(unbalancedInsert(t,e))
    
  } ensuring(res => 
    isAVL(res) && 
    height(res) >= height(t) && 
    height(res) <= height(t) + 1 && 
    size(res) <= size(t) + 1 &&
    content(res) == content(t) ++ Set[Int](e)
  )
     
  // O(nlogn)
  def balance(t:Tree) : Tree = {
    require(offByOne(t)) //isBST(t) && 
    t match {
      case Leaf() => Leaf() // impossible...
      case Node(l, v, r) => 
        val bfactor = balanceFactor(t)
        // at this point, the tree is unbalanced
        if(bfactor > 1 ) { // left-heavy
          val newL = 
            if (balanceFactor(l) < 0) { // l is right heavy
              rotateLeft(l)
            }
            else l
          rotateRight(Node(newL,v,r))
        }
        else if(bfactor < -1) { //right-heavy
          val newR = 
            if (balanceFactor(r) > 0) { // r is left heavy
              rotateRight(r)
            }
            else r
          rotateLeft(Node(l,v,newR))
        } else t        
      } 
    } ensuring(res => isAVL(res) && content(res) == content(t))

  def rotateRight(t:Tree) = {    
    t match {
      case Node(Node(ll, vl, rl),v,r) =>
        
        val hr = max(height(rl),height(r)) + 1        
        Node(ll, vl, Node(rl,v,r))
        
      case _ => t // this should not happen
  } }
   
 
  def rotateLeft(t:Tree) =  {    
    t match {
      case Node(l, v, Node(lr,vr,rr)) => 
                
        val hl = max(height(l),height(lr)) + 1        
        Node(Node(l,v,lr), vr, rr)
      case _ => t // this should not happen
  } } 

 /* 
  def psr (input : Int) : Int = {
    (input * 476272 + 938709) % 187987
  }
  def rec(size : Int, acc : Tree) : Tree = {
    if (size == 0) acc
    else rec(size -1, avlInsert(acc, psr(size)))
  }

 
  def test(size : Int) : Tree = { 
    
    rec(size, Leaf())

  }
*/
  
  @verified
  def test(t:Tree, i:Int) = { 
    //require(isAVL(t))
    avlInsert(t,i)
  }
  @verified
  def init() = Leaf()

}
