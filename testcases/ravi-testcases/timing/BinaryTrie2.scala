import leon.Utils._
import scala.collection.immutable.Set

object BinaryTrie { 
  
//  sealed abstract class CList
//  case class Cons(head: Node, tail: CList) extends CList
//  case class Nil() extends CList
    
  sealed abstract class Tree
  case class Leaf() extends Tree  
  case class Node(nvalue: Int, left : Tree, right: Tree) extends Tree
  
  sealed abstract class IList
  case class Cons(head: Int, tail: IList) extends IList
  case class Nil() extends IList  
  
  def listSize(l: IList): Int = (l match {
    case Nil() => 0
    case Cons(x, xs) => 1 + listSize(xs) 
  }) 
  
//  def fanOutBound(t : NAryTree, n: Int) : Boolean = { 
//    require(n >= 0)    
//    t match {    
//    	case Leaf() => true
//    	case Node(x, ch) =>  childSize(ch) <= n //&& fanOutBoundRec(ch, n)
//  }} //ensuring(res => true template((a) => a <= 0))
//  
//  def mult(x : Int, y : Int) : Int = {
//    require(x >= 0 && y >= 0)
//      if(x == 0 || y == 0) 0      
//      else
//    	  mult(x,y-1) + x 
//  } //ensuring(res => true template((a) => a <= 0))
  
  def find(inp: IList, t: Tree) : Tree = {
   inp match {
    case Nil() => t
    case Cons(x, Nil()) => t
    case Cons(x ,xs@Cons(y, _)) => {
       t match {
        case Leaf() => t
        case Node(v, l, r) => {        	
        	if(y > 0) find(xs, l) else find(xs, r)    	
        } 
      }           
    }
    case _ => t
   } 
  } ensuring(res => true template((a,c) => time <= a*listSize(inp)  + c))
  
  def insert(inp: IList, t: Tree): Tree = {    
    //require(n >= 0 && fanOutBound(t, n))
  inp match {
    case Nil() => t
    case Cons(x, Nil()) => t
    case Cons(x ,xs@Cons(y, _)) => {
       t match {
        case Leaf() => Node(y, Leaf(), Leaf())
        case Node(v, l, r) => {        	
        	val ch = if(y > 0) l else r
        	val newch = if(ch == Leaf()) Node(y, Leaf(), Leaf())
        				else ch
        	  if(y > 0)
        		  Node(v, insert(xs, newch), r)
        	  else 
        	    Node(v, l, insert(xs, newch))        	
        } 
      }           
    }
    case _ => t
  }   
} ensuring(res => true template((a,c) => time <= a*listSize(inp)  + c) )   
}
