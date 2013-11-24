import leon.Utils._
object Size
{
	sealed abstract class Tree
  	case class Node(left: Tree, value: Int, right: Tree) extends Tree
  	case class Leaf() extends Tree
  	
  	def size(t: Tree) : Int = {
	  t match {
	  	case Leaf() => 0
	  	case Node(l,x,r) => size(l) + size(r) + 1
	  }
	} ensuring(res => res >= 0)
	
//	def deepCopy(t: Tree) : Tree = {
//	  t match {
//	  	case Leaf() => Leaf()
//	  	case Node(l,x,r) => Node(deepCopy(l),x,deepCopy(r))
//	  	}
//	} ensuring(res => res == t)
	//ensuring(res => true template((a,b) => time <= a*res + b))	
} 