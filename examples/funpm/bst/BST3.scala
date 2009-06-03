package funpm.bst

object BST3 extends Application {
  
  sealed abstract case class BST() {
    // patterns are exhaustive, disjoint and all reachable
    def contains(key: Int): Boolean = this match {
      case Node(_,value,_) =>
        if(key == value) {
          true
        }
        else {
          this match {  
            case Node(left,value,_) if key < value => left.contains(key)
            case Node(_,value,right) if key > value => right.contains(key)
          }
        } 
      case e => false
    }
  }
  
  case class Empty() extends BST
  case class Node(val left: BST, val value: Int, val right: BST) extends BST
  
  
  
  // main, only for testing purposes
  assert(Node(Node(Empty(),3,Empty()),5,Empty()).contains(3))
}
