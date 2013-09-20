import leon.Utils._

object SizeAndLeftHeight
{
	sealed abstract class Tree
  	case class Node(left: Tree, value: Int, right: Tree) extends Tree
  	case class Leaf() extends Tree
  	
  	case class Tuple1(x: Int, y: Int)
  	
  	def sizeNheight(t: Tree) : Tuple1 = {
	  t match {
	  	case Leaf() => Tuple1(0,0)
	  	case Node(l,x,r) => {
	  	  val lval = sizeNheight(l);
	  	  val rval = sizeNheight(r);
	  	  Tuple1(lval.x+rval.x+1,lval.y+1)
	  	}
	  }	  
	} ensuring(res => res.x != res.y -1 template((a,b) => a* res.x + b*res.y >= 0))
	//ensuring(res => res._1 >= res._2 && res._1  >= 0)	    
	//ensuring(res => res._1 >= res_2.1)	 
} 