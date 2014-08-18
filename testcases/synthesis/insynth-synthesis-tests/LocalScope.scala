import leon.lang._

object LocalScope {
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color
 
  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  sealed abstract class OptionInt
  case class Some(v : Int) extends OptionInt
  case class None() extends OptionInt

  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_, l, v, r) => {
      // hide r
    	val r: Int = 5
    	//val f: ((Int, Int) => Boolean) = (x: Int, y: Int) => false
    	
	    Some(5) match {
	      case Some(newInt) => hole(0)    	    
	    }
    	
    	false
    } 
      
    case Empty() => true
  }
}
