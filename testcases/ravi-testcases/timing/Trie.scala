import leon.Utils._
import scala.collection.immutable.Set

object Trie { 
  
  sealed abstract class CList
  case class Cons(head: Node, tail: CList) extends CList
  case class Nil() extends CList
    
  sealed abstract class NAryTree
  case class Leaf() extends NAryTree  
  case class Node(nvalue: Int, children : CList) extends NAryTree
  
  sealed abstract class IList
  case class Elem(head: Int, tail: IList) extends IList
  case class Emp() extends IList

  def childSize(l: CList): Int = (l match {
    case Nil() => 0
    case Cons(x, xs) => 1 + childSize(xs)
  }) 
  
  def listSize(l: IList): Int = (l match {
    case Emp() => 0
    case Elem(x, xs) => 1 + listSize(xs) 
  }) 
    
  /*def treeSize(t: NAryTree): Int = {      
    (t match {
      case Empty() => 1
      case Node(_, ch) => 1 + childSize(ch)
    })
  } */
  //ensuring (res => true template((a,b) => twopower(blackHeight(t)) <= a*res + b))
  
  def findChild(v : Int, ch : CList) : NAryTree = {
    ch match {
      case Nil() => Leaf() 
      case Cons(x, xs) => if(x.nvalue == v) x else findChild(v, xs) 
    }
  } ensuring(res => true template((a,b) => time <= a*childSize(ch) + b))
  
  def append(v : Node, l : CList)  : CList = {
    l match {
      case Nil() => Cons(v, Nil())
      case Cons(x, xs) => Cons(x, append(v, xs))
    }
  } ensuring(res => true template((a,b) => time <= a*childSize(l) + b))
  
  /*def fanOutBoundRec(ch: CList, n : Int) : Boolean = {
    ch match {
      case Nil() => true
      case Cons(x, xs) => fanOutBound(x, n) && fanOutBoundRec(xs, n)
    }
  }*/ //ensuring(res => true template((a) => a <= 0))
  
  def fanOutBound(t : NAryTree, n: Int) : Boolean = { 
    require(n >= 0)    
    t match {    
    	case Leaf() => true
    	case Node(x, ch) =>  childSize(ch) <= n //&& fanOutBoundRec(ch, n)
  }} //ensuring(res => true template((a) => a <= 0))
  
  def mult(x : Int, y : Int) : Int = {
    require(x >= 0 && y >= 0)
      if(x == 0 || y == 0) 0      
      else
    	  mult(x,y-1) + x 
  } //ensuring(res => true template((a) => a <= 0))
  
  def insert(elem: IList, t: NAryTree, n: Int): NAryTree = {
    require(n >= 0 && fanOutBound(t, n))
        
    elem match {
      case Emp()  => t
      case Elem(_, Emp()) => t
      case Elem(_, nx@Elem(v, _)) => t match {
        case Leaf() => insert(nx, Node(v, Nil()), n)
        case Node(x, ch) => {
        	//pick a children to insert (if none exists create a new children)
        	val chNode = findChild(v, ch)
        	if(chNode == Leaf()) {
        	  //append a new child
        	  val newNode = Node(v, Nil())
        	  insert(nx, Node(x, append(newNode, ch)), n)
        	}
        	else insert(nx, chNode, n)      
        } 
      }      
      case _ => t
    }
  } ensuring (res => true template((a,b,c,d) => time <= a*mult(n, listSize(elem)) + b*listSize(elem) + d))   
}
