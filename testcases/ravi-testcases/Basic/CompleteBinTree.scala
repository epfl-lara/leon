object CompleteBinTreee
{
	sealed abstract class Tree
  	case class Node(left: Tree, value: Int, right: Tree) extends Tree
  	case class Leaf() extends Tree
  	
  	def complete(t: Tree) : Boolean = {
	  t match {
	  	case Leaf() => true
	  	case Node(l,x,r) => (height(l) == height(r)) && complete(l) && complete(r) 
	  }
	}
  	
  	def height(t: Tree): Int = {
	  t match{
	    case Leaf() => 0
	    case Node(l,x,r) => {
	      val hl = height(l)
	      val hr = height(r)
	      if(hl > hr) hl + 1 else hr + 1	    
	    }
	  }
	}
  	
  	def size(t: Tree) : Int = {
	  t match {
	  	case Leaf() => 0
	  	case Node(l,x,r) => size(l) + size(r) + 1
	  }
	} ensuring (res => (!complete(t) || twopower(height(t)) - 1 != res - 1))    
	//ensuring (res => (!complete(t) || twopower(height(t)) - 1 <= res))
	
	def twopower(x: Int) : Int = {		   
    	if(x < 1) 1 else 2* twopower(x - 1)    
	}
} 