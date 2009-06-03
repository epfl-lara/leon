package contracts.bst

object BSTAsSet extends Application {
  sealed abstract case class BST(/*: specvar */ content : Set[Int]) {
    // patterns are exhaustive, disjoint and all reachable     
    def add(x: Int): BST = {
      this match {
        case Empty(_) => Node(Set(x), 
			      Empty(Set.empty),x,Empty(Set.empty))
        case Node(_,left,v,right) if (x < v) => Node(content + x, 
						   left.add(v), v, right)
        case Node(_,left,v,right) if (x > v) => Node(content + x, 
						   left, v, right.add(x))
        case Node(_,_,v,_) if (v == x) => this
      }
    } ensuring(result => (result.content == content + x))

    // patterns are exhaustive, disjoint and all reachable 
    def contains(key: Int): Boolean = {
      this match { 
        case Node(_,left,v,_) if (key < v) => left.contains(key)
        case Node(_,_,v,right) if (key > v) => right.contains(key)
        case Node(_,_,v, _) if (key == v) => true
        case Empty(_) => false
      }
    } ensuring(res => (res == content.contains(key)))
  }
  
  case class Empty(override val content : Set[Int]) extends BST(Set.empty)
  case class Node(override val content : Set[Int], val left: BST, val value: Int, val right: BST) extends BST(content)

  val empt = Empty(Set.empty)
  
  // main, only for testing purposes
  val t = empt.add(3).add(5).add(17)
  println(t);
  println(t.contains(3))
}
