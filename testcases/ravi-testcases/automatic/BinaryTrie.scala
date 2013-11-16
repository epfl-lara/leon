import leon.Utils._
import scala.collection.immutable.Set

object BinaryTrie {    
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
  
  def height(t: Tree): Int = {
	  t match{
	    case Leaf() => 0
	    case Node(x,l,r) => {
	      val hl = height(l)
	      val hr = height(r)
	      if(hl > hr) hl + 1 else hr + 1	    
	    }
	  }
  } 
  
//  def firstMatch(l : IList, t : Tree) : Boolean = {
//    l match {
//      case Nil() => false
//      case Cons(x, xs) => t match {    
//    	case Leaf() => false
//    	case Node(y, ch) => x == y 
//      } 
//    }    
//  } 
  
//  def find(inp: IList, t: Tree) : Tree = {
//    //require(firstMatch(inp, t))
//   inp match {
//    case Nil() => t
//    case Cons(x, Nil()) => t
//    case Cons(x ,xs@Cons(y, _)) => {
//       t match {
//        case Leaf() => t
//        case Node(v, l, r) => {        	
//        	if(y > 0) find(xs, l) else find(xs, r)    	
//        } 
//      }           
//    }
//    case _ => t
//   } 
//  } 
  //ensuring(res => true template((a,c) => time <= a*listSize(inp)  + c))
  
  def insert(inp: IList, t: Tree): Tree = {    
    //require(firstMatch(inp,t))
    
    t match {
        case Leaf() => {
          inp match {
            case Nil() => t
            case Cons(x ,xs) => {             
              val newch = insert(xs, Leaf())
              newch match {
                case Leaf() => Node(x, Leaf(), Leaf())
                case Node(y, _, _) => if(y > 0) Node(x, newch, Leaf()) else Node(y, Leaf(), newch)
              }               
            }
          }
          
        }
        case Node(v, l, r) => {       
          inp match {
            case Nil() => t
            case Cons(x, Nil()) => t
            case Cons(x ,xs@Cons(y, _)) => {
              val ch = if(y > 0) l else r
//        	val newch = if(ch == Leaf()) Node(y, Leaf(), Leaf())
//        				else ch
        	  if(y > 0)
        		  Node(v, insert(xs, ch), r)
        	  else 
        	    Node(v, l, insert(xs, ch))
            }  
            case _ => t
        } 
      }
    }
    
//  inp match {
//    case Nil() => t
//    case Cons(x, Nil()) => t
//    case Cons(x ,) => {
//                  
//    }
//    case _ => t
//  }   
} 
  
  def create(inp: IList) : Tree = {
//    inp match {
//      case Nil() => Leaf()
//      case Cons(x, xs) => insert(inp, Node(x, Leaf(), Leaf()))
//    }
    insert(inp, Leaf())
  }ensuring(res => height(res) >= listSize(inp))
  //ensuring(res => true template((a,c) => time <= a*listSize(inp)  + c) )   
}
