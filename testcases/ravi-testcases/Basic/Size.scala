import leon.lang.invariantLang._
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
} 