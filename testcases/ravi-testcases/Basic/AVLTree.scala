import leon.Utils._

object AVLTree  {
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left : Tree, value : Int, right: Tree, rank : Int) extends Tree

/*  sealed abstract class OptionInt
  case class None() extends OptionInt
  case class Some(i:Int) extends OptionInt
*/

/*  def smallerOption(o1:OptionInt,o2:OptionInt) : Boolean  = {
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
  )*/

  def min(i1:Int, i2:Int) : Int = if (i1<=i2) i1 else i2
  def max(i1:Int, i2:Int) : Int = if (i1>=i2) i1 else i2
  
   def twopower(x: Int) : Int = {
    require(x >= 0)
    if(x < 1) 1    
    else      
      2* twopower(x - 1)
  } ensuring(_ >= 0 template((a) => a <= 0))

  def size(t: Tree): Int = {
    require(isAVL(t))  
    (t match {
      case Leaf() => 0
      case Node(l, _, r,_) => size(l) + 1 + size(r)
    })
  } ensuring (res => true template((a,b) => twopower(h(t)) <= 4*res + 2))
  
  def h(t:Tree) : Int = (t match {
    case Leaf() => 0
    case Node(l,_,r,_) => if(h(l) >= h(r)) 
    	h(l) + 1 
      else 
        h(r) + 1
  }) ensuring(_ >= 0 template((a) => a <= 0))

  def rank(t:Tree) : Int = (t match {
    case Leaf() => 0
    case Node(l,_,r,h) => h  
  }) 

/*  def treeMax(t:Tree) : OptionInt = {
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
  }*/



  def balanceFactor(t:Tree) : Int = t match {
    case Leaf() => 0
    case Node(l,_,r,_) => h(l) - h(r)
  }
  
  /*def rankHeight(t: Tree) : Boolean = t match {
    case Leaf() => true 
    case Node(l,_,r,rk) => rankHeight(l) && rankHeight(r) && rk == h(t)
  }*/

  def isAVL(t:Tree) : Boolean = {
    //isBST(t) && rankHeight(t) &&
    (t match {
        case Leaf() => true
        case Node(l,_,r,rk) => 
          isAVL(l) && isAVL(r) && balanceFactor(t) >= -1 && balanceFactor(t) <= 1 //&& rk == h(t) 
      })    
  } //ensuring (res => true template((a,b) => time <= a*h(t) + b))

/* def bstMax(t:Tree) : OptionInt = {
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
  } ensuring (res => res == treeMin(t))*/
 
/*  def unbalancedInsert(t: Tree, e : Int) : Tree = {
    //require(isAVL(t))
    t match {
      case Leaf() => Node(Leaf(), e, Leaf(), 1)
      case Node(l,v,r,h) => 
             if (e == v) t
        else if (e <  v) Node(avlInsert(l,e), v, r, h)
        else             Node(l, v, avlInsert(r,e), h)
    }
  } //ensuring( res => isBST(res) && rankHeight(t))
                    
  def avlInsert(t: Tree, e : Int) : Tree = {    
    require(isAVL(t))
    
    balance(unbalancedInsert(t,e))
    
  } ensuring ( res => true template((a,b) => time <= a*h(t) + b))
     
  def balance(t:Tree) : Tree = {
    //require(isBST(t) && rankHeight(t))
    //if (isAVL(t)) t
    //else 
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
  } //ensuring(isAVL(_))

  def rotateRight(t:Tree) = {
    //require(isBST(t))
    t match {
      case Node(Node(ll, vl, rl, _),v,r, _) =>
        
        val hr = max(rank(rl),rank(r)) + 1        
        Node(ll, vl, Node(rl,v,r,hr), max(rank(ll),hr) + 1)
        
      case _ => t // this should not happen
  } } //ensuring(isBST(_))
   
 
  def rotateLeft(t:Tree) =  {
    //require(isBST(t))
    t match {
      case Node(l, v, Node(lr,vr,rr,_), _) => 
                
        val hl = max(rank(l),rank(lr)) + 1        
        Node(Node(l,v,lr,hl), vr, rr, max(hl, rank(rr)) + 1)
      case _ => t // this should not happen
  } } //ensuring(isBST(_))
*/
}
    
