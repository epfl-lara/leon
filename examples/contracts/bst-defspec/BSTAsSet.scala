package contracts.bstdefspec

object BSTAsSet extends Application {
  sealed abstract class BST
  case class Empty() extends BST
  case class Node(left: BST, value: Int, right: BST) extends BST

  def content(t : BST) : Set[Int] = t match {
    case Empty() => Set.empty
    case Node(left,v,right) => (content(left) ++ Set(v) ++ content(right))
  }

  def size(t : BST) : Int = t match {
    case Empty() => 0
    case Node(left,v,right) => size(left) + 1 + size(right)
  }

  def add(x : Int, t : BST) : BST = {
    t match {
      case Empty() => Node(Empty(),x,Empty())
      case Node(left,v,right) => {
	if (x < v) 
	  Node(add(x, left), v, right)
	else if (x==v) t
	else
	  Node(left, v, add(x, right))
      }
    }
  } // ensuring(result => (content(result) == content(t) + x))

  def contains(key: Int, t : BST): Boolean = { 
    t match {
      case Empty() => false
      case Node(left,v,right) => {
	if (key == v) true
	else if (key < v) contains(key, left)
	else contains(key, right)
      }
      }
  } // ensuring(res => (res == content(t).contains(key)))

  // executable functions that 'illustrate' the meaning of quantifiers
  def forallTree(property : (BST => Boolean)) : Boolean = {
    property(Empty()) &&
    property(Node(Empty(), 3, Empty())) &&
    property(Node(Node(Empty(), 3, Empty()), 5, Node(Empty(), 7, Empty())))
    // if it holds for these trees, why wouldn't it hold in general?
  }
  def forallInt(property : (Int => Boolean)) : Boolean = {
    property(0) &&
    property(1) &&
    property(2) &&
    property(3) &&
    property(-2)
  }

  // main, only for testing purposes
  val t = add(17, add(6, add(3, add(5, add(3, Empty())))))
  println(t)
  println(content(t))
  println(size(t))
  println(contains(5, t))

  // instead of contracts, we can write global assertions:
  println(
    forallInt(x => forallTree(t =>
	content(add(x, t)) == content(t) + x)))
  println(
    forallInt(x => forallTree(t =>
	(contains(x,t) == content(t).contains(x)))))
}
