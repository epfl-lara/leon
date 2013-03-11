object SizeAndLeftHeight
{
	sealed abstract class Tree
  	case class Node(left: Tree, value: Int, right: Tree) extends Tree
  	case class Leaf() extends Tree
  	
  	def sizeNheight(t: Tree) : (Int,Int) = {
	  t match {
	  	case Leaf() => (0,0)
	  	case Node(l,x,r) => {
	  	  val (a,b) = sizeNheight(l);
	  	  val (c,d) = sizeNheight(r);
	  	  (a+c+1,b+1)
	  	}
	  }	  
	} ensuring(res => res._1 != res._2 -1) 
	//ensuring(res => res._1 >= res._2 && res._1  >= 0)	    
	//ensuring(res => res._1 >= res_2.1)	 
} 