import leon.lang._

object LinkedSet {

  case class Node(element: Int, var next: Option[Node])


  def insert(root: Node, element: Int): Unit = {
    //not sure how to get to the end without duplicating pointer to root?
    ()
  }
}
