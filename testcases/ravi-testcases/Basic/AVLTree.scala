import leon.Utils._

object AVLTree  {
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left : Tree, value : Int, right: Tree) extends Tree

  /*sealed abstract class OptionInt
  case class None() extends OptionInt
  case class Some(i:Int) extends OptionInt
*/

  /*def smallerOption(o1:OptionInt,o2:OptionInt) : Boolean  = {
    (o1,o2) match {
      case (Some(i1), Some(i2)) => i1 < i2
      case (_,_) => true
    }
  }*/

  /*def minOption(o1:OptionInt,o2:OptionInt) : OptionInt = (
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
  
  def h(t:Tree) : Int = (t match {
    case Leaf() => 0
    case Node(l,_,r) => max(h(l), h(r)) + 1

  })

  def height(t:Tree) : Int = (t match {
    case Leaf() => 0
    case Node(l,_,r) => max(height(l), height(r)) + 1
    
  }) //ensuring(res => res >= 0 template((a,b) => time <= a*h(t) + b))

/*  def treeMax(t:Tree) : OptionInt = {
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
  }*/

  
  /*def isBST(t:Tree) : Boolean = {
    t match {
      case Leaf() => true
      case Node(l,v,r) => 
        if (isBST(l) && isBST(r)) {
          smallerOption(Some(v),bstMin(r)) && 
          smallerOption(bstMax(l),Some(v))
        }
        else false 
    }
  }*/



  def balanceFactor(t:Tree) : Int = t match {
    case Leaf() => 0
    case Node(l,_,r) => 
      height(l) - height(r)
  }

  def isAVL(t:Tree) : Boolean = {
    //isBST(t) && 
    t match {
        case Leaf() => true
        case Node(l,_,r) => 
          isAVL(l) && isAVL(r) && balanceFactor(t) >= -1 && balanceFactor(t) <= 1   
      }    
  } //ensuring (res => true template((a,b) => time <= a*h(t) + b))

/* def bstMax(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None() 
      case Node(_,v,Leaf()) => Some(v) 
      case Node(_,_,r)      => bstMax(r)
    }
  } ensuring (res => res == treeMax(t) template((a,b) => time <= a*height(t) + b))

  def bstMin(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None()
      case Node(Leaf(),v,_) => Some(v) 
      case Node(l, _ ,_ ) => bstMin(l)
    }
  } ensuring (res => res == treeMin(t) template((a,b) => time <= a*height(t) + b))
*/ 
  def unbalancedInsert(t: Tree, e : Int) : Tree = {
    //require(isAVL(t))
    t match {
      case Leaf() => Node(Leaf(), e, Leaf())
      case Node(l,v,r) => 
             if (e == v) t
        else if (e <  v) Node(avlInsert(l,e), v, r)
        else             Node(l, v, avlInsert(r,e))
    }
  } //ensuring( res => isBST(res) )
                    
  def avlInsert(t: Tree, e : Int) : Tree = {
    require(isAVL(t))
    balance(unbalancedInsert(t,e))
  } ensuring ( res => true template((a,b) => time <= a*h(t) + b))
     
  def balance(t:Tree) : Tree = {
    //require(isBST(t))
    //if (isAVL(t)) t
    //else 
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
        else if(bfactor < -1) {
          val newR = 
            if (balanceFactor(r) > 0) { // r is left heavy
              rotateRight(r)
            }
            else r
          rotateLeft(Node(l,v,newR))
        } else t        
      } 
  } //ensuring(isAVL(_))

  def rotateRight(t:Tree) = {
    //require(isBST(t))
    t match {
      case Node(Node(ll, vl, rl),v,r) =>
        Node(ll, vl, Node(rl,v,r))  
      case _ => t // this should not happen
  } } //ensuring(isBST(_))
   
 
  def rotateLeft(t:Tree) =  {
    //require(isBST(t))
    t match {
      case Node(l, v, Node(lr,vr,rr)) => 
        Node(Node(l,v,lr), vr, rr)
      case _ => t // this should not happen
  } } //ensuring(isBST(_))

}
    
