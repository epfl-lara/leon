/* Copyright 2009-2015 EPFL, Lausanne
 *
 * Author: Manos (modified by Ravi)
 * Date: 20.11.2013
 **/

import leon.lang._

object AVLTree  {
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left : Tree, value : Int, right: Tree, rank : Int) extends Tree

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

  def rank(t: Tree) : Int = {
    t match {
      case Leaf() => 0
      case Node(_,_,_,rk) => rk
    }
  }

  def size(t: Tree): Int = {
    (t match {
      case Leaf() => 0
      case Node(l, _, r,_) => size(l) + 1 + size(r)
    })
  } ensuring (_ >= 0)
  
  def height(t: Tree): Int = {
    t match {
      case Leaf() => 0
      case Node(l, x, r, _) => {
        val hl = height(l)
        val hr = height(r)
        if (hl > hr) hl + 1 else hr + 1
      }
    }
  } ensuring(_ >= 0)

  def treeMax(t:Tree) : OptionInt = {
    t match {
      case Leaf()      => None()
      case Node(l,v,r,_) => maxOption(Some(v), maxOption (treeMax(l), treeMax(r)))
    }
  }

  def treeMin(t:Tree) : OptionInt = {
    t match {
      case Leaf()      => None()
      case Node(l,v,r,_) => minOption(Some(v), minOption (treeMin(l), treeMin(r)))
    }
  }

  
  def isBST(t:Tree) : Boolean = {
    t match {
      case Leaf() => true
      case Node(l,v,r,_) => 
        if (isBST(l) && isBST(r)) {
          smallerOption(Some(v),bstMin(r)) && 
          smallerOption(bstMax(l),Some(v))
        }
        else false 
    }
  }

  def rankHeight(t: Tree) : Boolean = t match {
    case Leaf() => true 
    case Node(l,_,r,rk) => rankHeight(l) && rankHeight(r) && rk == height(t)
  }
  
  def balanceFactor(t : Tree) : Int = {
    t match{
      case Leaf() => 0
      case Node(l, _, r, _) => rank(l) - rank(r)
    }
  } 

  def isAVL(t:Tree) : Boolean = {    
    t match {
        case Leaf() => true        
        case Node(l,_,r,rk) =>  isAVL(l) && isAVL(r) && balanceFactor(t) >= -1 && balanceFactor(t) <= 1 && rankHeight(t) //isBST(t) && 
      }    
  } 

 def bstMax(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None() 
      case Node(_,v,Leaf(),_) => Some(v) 
      case Node(_,_,r,_)      => bstMax(r)
    }
  } ensuring (res => res == treeMax(t))

  def bstMin(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None()
      case Node(Leaf(),v,_,_) => Some(v) 
      case Node(l, _ ,_ ,_) => bstMin(l)
    }
  } ensuring (res => res == treeMin(t))
  
  def offByOne(t : Tree) : Boolean = {
    t match {
      case Leaf() => true
      case Node(l,_,r,_) => isAVL(l) && isAVL(r) && balanceFactor(t) >= -2 && balanceFactor(t) <= 2 
    }
  }
 
  def unbalancedInsert(t: Tree, e : Int) : Tree = {
    require(isAVL(t))
    t match {
      case Leaf() => Node(Leaf(), e, Leaf(), 1)
      case Node(l,v,r,h) => 
             if (e == v) t
        else if (e <  v){
          val newl = avlInsert(l,e)
          Node(newl, v, r, max(rank(newl), rank(r)) + 1)
        } 
        else {
          val newr = avlInsert(r,e)
          Node(l, v, newr, max(rank(l), rank(newr)) + 1)
        }            
    }
  } 
                    
  def avlInsert(t: Tree, e : Int) : Tree = {    
    require(isAVL(t))
    
    balance(unbalancedInsert(t,e))
    
  } ensuring(res => isAVL(res) && rank(res) >= rank(t) && rank(res) <= rank(t) + 1 && size(res) <= size(t) + 1)
     
  def balance(t:Tree) : Tree = {
    require(rankHeight(t) && offByOne(t)) //isBST(t) && 
    t match {
      case Leaf() => Leaf() // impossible...
      case Node(l, v, r, h) => 
        val bfactor = balanceFactor(t)
        // at this point, the tree is unbalanced
        if(bfactor > 1 ) { // left-heavy
          val newL = 
            if (balanceFactor(l) < 0) { // l is right heavy
              rotateLeft(l)
            }
            else l
          rotateRight(Node(newL,v,r, max(rank(newL), rank(r)) + 1))
        }
        else if(bfactor < -1) {
          val newR = 
            if (balanceFactor(r) > 0) { // r is left heavy
              rotateRight(r)
            }
            else r
          rotateLeft(Node(l,v,newR, max(rank(newR), rank(l)) + 1))
        } else t        
      } 
  } ensuring(isAVL(_))

  def rotateRight(t:Tree) = {    
    t match {
      case Node(Node(ll, vl, rl, _),v,r, _) =>
        
        val hr = max(rank(rl),rank(r)) + 1        
        Node(ll, vl, Node(rl,v,r,hr), max(rank(ll),hr) + 1)
        
      case _ => t // this should not happen
  } }
   
 
  def rotateLeft(t:Tree) =  {    
    t match {
      case Node(l, v, Node(lr,vr,rr,_), _) => 
                
        val hl = max(rank(l),rank(lr)) + 1        
        Node(Node(l,v,lr,hl), vr, rr, max(hl, rank(rr)) + 1)
      case _ => t // this should not happen
  } } 
}
    
