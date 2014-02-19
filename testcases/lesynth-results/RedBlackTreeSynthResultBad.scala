import leon.annotation._
import leon.lang._

object RedBlackTree { 
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color
 
  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  def content(t: Tree) : Set[Int] = t match {
    case Empty() => Set.empty
    case Node(_, l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def size(t: Tree) : Int = t match {
    case Empty() => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }

  /* We consider leaves to be black by definition */
  def isBlack(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(),_,_,_) => true
    case _ => false
  }

  def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def redDescHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(_,l,_,r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }

  def blackHeight(t : Tree) : Int = t match {
    case Empty() => 1
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
  }
  
  def balance(c: Color, a: Tree, x: Int, b: Tree): Tree = {
    Node(c,a,x,b) match {
      case Node(Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(c,a,xV,b) => Node(c,a,xV,b)
    }
  } ensuring (res => content(res) == content(Node(c,a,x,b)))

  // <<insert element x into the tree t>>
  def ins(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
//    t match {
//      case Empty() => Node(Red(),Empty(),x,Empty())
//      case Node(c,a,y,b) =>
//        if      (x < y)  balance(c, ins(x, a), y, b)
//        else if (x == y) Node(c,a,y,b)
//        else             balance(c,a,y,ins(x, b))
//    }
    if ((redNodesHaveBlackChildren(t) && blackBalanced(t))) {
      (t match {
        case Empty() =>
          Node(Red(), Empty(), x, Empty())
        case n: Node =>
          if ((n.value == x)) {
            Node(n.color, n.left, x, n.right)
          } else {
            balance(n.color, n.right, n.value, ins(x, n.left))
          }
      })
    } else {
      leon.lang.error[Tree]("Precondition failed")
    }
  } ensuring (res => content(res) == content(t) ++ Set(x) 
                   && size(t) <= size(res) && size(res) <= size(t) + 1
                   && redDescHaveBlackChildren(res)
                   && blackBalanced(res))

}
