object CountDiff
{
	sealed abstract class Tree
  	case class Node(left: Tree, value: Int, right: Tree) extends Tree
  	case class Leaf() extends Tree
  	
  	def CountDiff(a : Tree, b: Tree) : Int = {
	  (a,b) match {
	    case (Leaf(),Leaf()) => 0 
	  	case _ => {	  	 
	  	  a match{
	  	    case Node(la,x,ra) => {
	  	      b match{	  	        
	  	        case Node(lb,y,rb) => CountDiff(la,lb) + CountDiff(ra,rb)
	  	        //there is a difference of one in the following case
	  	        case _ => 1 + CountDiff(la,b) + CountDiff(ra,b)
	  	      }
	  	    }
	  	    case _ => b match{	  	        
	  	        case Node(lb,y,rb) =>  CountDiff(a,lb) + CountDiff(a,rb) - 1	  	 
	  	        case _ => 0
	  	      } 
	  	  }
	  	}
	  }	  
	}  ensuring(res => res == size(a) - size(b))
	//ensuring(res => res._1 >= res_2.1)
	
	def size(t: Tree) : Int = {
	  t match {
	  	case Leaf() => 0
	  	case Node(l,x,r) => size(l) + size(r) + 1
	  }
	} //ensuring (res => res >= 0)
} 