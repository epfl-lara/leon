package testcases


object UnificationTest {

  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree

  // Proved by unifier
  def mkTree(a: Int, b: Int, c: Int) = {
    Node(Node(Leaf(), a, Leaf()), b, Node(Leaf(), c, Leaf()))
    //Node(Leaf(), b, Node(Leaf(), c, Leaf()))
  } ensuring ( res => {
    res.left != Leaf() &&
    res.value == b &&
    res.right == Node(Leaf(), c, Leaf())
  })



  sealed abstract class Term
  case class F(t1: Term, t2: Term, t3: Term, t4: Term) extends Term
  case class G(s1: Term, s2: Term) extends Term
  case class H(r1: Term, r2: Term) extends Term
  case class A extends Term
  case class B extends Term

  def examplePage268(x1: Term, x2: Term, x3: Term, x4: Term, x5: Term) = {
    F(G(H(A(), x5), x2), x1, H(A(), x4), x4)
  } //ensuring ( _ == F(x1, G(x2, x3), x2, B()) )



  case class Tuple3(_1: Term, _2: Term, _3: Term)

  def examplePage269(x1: Term, x2: Term, x3: Term, x4: Term) = {
    Tuple3(H(x1, x1), H(x2, x2), H(x3, x3))
  } /*ensuring ( res => {
    x2 == res._1 &&
    x3 == res._2 &&
    x4 == res._3
  })*/


  // Cannot be solved yet, due to the presence of an if expression
  def insert(tree: Tree, value: Int) : Node = (tree match {
    case Leaf() => Node(Leaf(), value, Leaf())
    case n @ Node(l, v, r) => if(v < value) {
      Node(l, v, insert(r, value))
    } else if(v > value) {
       Node(insert(l, value), v, r)
    } else {
      n
    }
  }) ensuring(_ != Leaf())

}
