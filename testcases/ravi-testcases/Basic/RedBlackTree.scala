import scala.collection.immutable.Set

object RedBlackTree { 
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color
 
  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  sealed abstract class OptionInt
  case class Some(v : Int) extends OptionInt
  case class None() extends OptionInt
     
  def twopower(x: Int) : Int = {
    //require(x >= 0)
    if(x < 1) 1    
    else      
      2* twopower(x - 1)
  } //ensuring (res => res >= 1)

  def size(t: Tree): Int = {
    require(blackBalanced(t))  
    (t match {
      case Empty() => 1
      case Node(_, l, v, r) => size(l) + 1 + size(r)
    })
  } ensuring (res => res >= (twopower(blackHeight(t)) - 1))   
    
  def blackHeight(t : Tree) : Int = {    
   t match {    
    case Empty() => 1
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
   	}
  } //ensuring (_ >= 1)
  
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
  } 

  def redDescHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(_,l,_,r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }
  
  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }        
  
  // <<insert element x into the tree t>>
  def ins(x: Int, t: Tree): (Tree,Int) = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
    
    t match {
      case Empty() => (Node(Red(),Empty(),x,Empty()), 0)
      case Node(c,a,y,b) =>
        if(x < y) {
        	val (t1,i) = ins(x, a)
        	(balance(c, t1, y, b), i + 1)
        }
        else if (x == y){
        	(Node(c,a,y,b), 0)
        }
        else{
          val (t1,i) = ins(x, b)
          (balance(c,a,y,t1), i + 1)
        } 
    }
  } //ensuring (res => true template((a,b) => a* res._2 <= 2 * blackHeight(t))) 
  //ensuring (res => res._2 <= 2 * blackHeight(t))                   

  def makeBlack(n: Tree): Tree = {
    n match {
      case Node(Red(),l,v,r) => Node(Black(),l,v,r)
      case _ => n
    }
  }  
  
  def add(x: Int, t: Tree): (Tree,Int) = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t) )
    val (t1,i) =  ins(x, t)
    (makeBlack(t1),i)
  } //ensuring (res => res._2 <= 2 * blackHeight(t))                
  //size(t) >= (twopower(blackHeight(t)) - 1) &&
  
  def balance(co: Color, l: Tree, x: Int, r: Tree): Tree = {        
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
      case Node(c,a,xV,b) => Node(c,a,xV,b)
    }
  } 
}
