import leon.Utils._
import scala.collection.immutable.Set

object RedBlackTree { 
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color
 
  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree
     
  def twopower(x: Int) : Int = {
    //require(x >= 0)
    if(x < 1) 1    
    else      
      2* twopower(x - 1)
  } 

  def size(t: Tree): Int = {
    require(blackBalanced(t))  
    (t match {
      case Empty() => 1
      case Node(_, l, v, r) => size(l) + 1 + size(r)
    })
  } ensuring (res => res != (twopower(blackHeight(t)) - 2) template((a,b,c) => a*res + b*twopower(blackHeight(t)) + c <= 0))   
    
  def blackHeight(t : Tree) : Int = {    
   t match {    
    case Empty() => 1
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
   	}
  }
  
  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }          
}
