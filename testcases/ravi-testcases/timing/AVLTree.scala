import leon.Utils._

/**
 * created by manos and modified by ravi.
 * BST property cannot be verified 
 */
object AVLTree  {
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left : Tree, value : Int, right: Tree, rank : Int) extends Tree


  def min(i1:Int, i2:Int) : Int = if (i1<=i2) i1 else i2
  def max(i1:Int, i2:Int) : Int = if (i1>=i2) i1 else i2  
  
  /*def twopower(x: Int) : Int = {
    //require(x >= 0)
    if(x < 1) 1    
    else      
      3/2 * twopower(x - 1)
  } ensuring(res => res >= 1 template((a) => a <= 0))*/
  
  def rank(t: Tree) : Int = {
    t match {
      case Leaf() => 0
      case Node(_,_,_,rk) => rk
    }
  }
  
  def height(t: Tree): Int = {
    t match {
      case Leaf() => 0
      case Node(l, x, r, _) => {
        val hl = height(l)
        val hr = height(r)
        max(hl,hr) + 1
      }
    }
  }

  def size(t: Tree): Int = {
    //require(isAVL(t))    
    (t match {
      case Leaf() => 0
      case Node(l, _, r,_) => size(l) + 1 + size(r)
    })
    
  } ensuring (res => true template((a,b) => height(t) <= a*res + b))  
  
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
 
  def unbalancedInsert(t: Tree, e : Int) : Tree = {    
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
    
    balance(unbalancedInsert(t,e))
    
  } ensuring(res => true template((a,b) => time <= a*height(t) + b))
  //minbound: ensuring(res => time <= 138*height(t) + 19)   
     
  def balance(t:Tree) : Tree = {    
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
  } 

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
    
