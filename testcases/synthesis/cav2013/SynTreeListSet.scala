import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object BinaryTree {
  // list of integers
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l:List): Int = (l match {
    case Nil() => 0
    case Cons(h,t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def size_syn(l:List):Int = choose((k:Int) =>
    k >= 0 &&
    (l match {
      case Nil() => k==0
      case Cons(_,Nil()) => k==1
      case Cons(_,Cons(_,Nil())) => k==2
      case Cons(_,Cons(_,Cons(_,Nil()))) => k > 2
      case _ => true
    })
  )

  // set of elements from l
  def l2s(l: List): Set[Int] = l match {
      case Nil() => Set()
      case Cons(i, t) => Set(i) ++ l2s(t)
  }

  def listFrom(k:Int) : List = {
    require(0 <= k)
    if (k==0) Nil()
    else Cons(k, listFrom(k-1))
  }
  def setFrom(k:Int) : Set[Int] = {
    require(0 <= k)
    if (k==0) Set.empty[Int]
    else Set(k) ++ setFrom(k-1)
  }

  def l2s_syn(l:List,k:Int):Set[Int] = {
    require(0 <= k)
    choose((res:Set[Int]) =>
      (l!=listFrom(k) || res==setFrom(k)) &&
      (l match {
	case Nil() => (res==Set.empty[Int])
	case Cons(x,Nil()) => res==Set(x)
	case Cons(x,Cons(y,Nil())) => res==Set(x,y)
	case Cons(x1,Cons(x2,Cons(x3,Cons(x4,Nil())))) => res==Set(x1,x2,x3,x4)
	case _ => true
      })
   )
  }

/* // For this, use the passes branch.
  def l2s_syn(l:List):Set[Int] = {
    choose((res:Set[Int]) =>
    passes(Map[List,Set[Int]](
      Nil() -> Set.empty[Int],
      Cons(100,Nil()) -> Set(100),
      Cons(200,Nil()) -> Set(200),
      Cons(300,Nil()) -> Set(300),
      Cons(1,Cons(2,Nil())) -> Set(1,2),
      Cons(100,Cons(200,Nil())) -> Set(100,200),
      Cons(1,Cons(2,Cons(3,Cons(4,Nil())))) -> Set(1,2,3,4)),
	   l, res))
  }
*/

  def l2s_syn2(l:List):Set[Int] = {
    choose((res:Set[Int]) => l2s(l)==res)
  }

  // tree of integers
  sealed abstract class Tree
  case class Node(left : Tree, value : Int, right : Tree) extends Tree
  case class Leaf() extends Tree

  // set of elements from t
  def t2s(t : Tree): Set[Int] = t match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => t2s(l) ++ Set(v) ++ t2s(r)
  }

  def t2s_syn(t:Tree) : Set[Int] = choose((res:Set[Int]) =>   
    t match {
      case Leaf() => res==Set.empty[Int]
      case Node(Leaf(),v,Leaf()) => res==Set(v)
      case Node(Node(Leaf(),v1,Leaf()),v2,Leaf()) => res==Set(v1,v2)
      case Node(Leaf(),v1,Node(Leaf(),v2,Leaf())) => res==Set(v1,v2)
      case _ => true
    }
  )

  // list of t, in order, in from of l0
  // list of t, in order, in from of l0
  def seqWith(t:Tree,l0:List) : List = (t match {
    case Leaf() => l0
    case Node(l, v, r) => seqWith(l,Cons(v,seqWith(r,l0)))
  }) ensuring (res => l2s(res) == t2s(t) ++ l2s(l0))

  def seqWith_syn(t:Tree,l0:List) : List = 
    choose((res:List) =>
      l2s(res) == t2s(t) ++ l2s(l0))

  // list of tree t
  def t2l(t:Tree) : List = ({ 
    seqWith(t,Nil())
  }) ensuring (res => l2s(res)==t2s(t))

  def t2l_syn(t:Tree) : List = 
    choose((res:List) => l2s(res)==t2s(t))
}
