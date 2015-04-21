import leon.annotation._
import leon.lang._

object BinaryTree {
  // list of integers
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // set of elements from l
  def l2s(l: List): Set[Int] = l match {
    case Nil() => Set()
    case Cons(i, t) => Set(i) ++ l2s(t)
  }

  // l has no duplicates, nor elements from s
  def noDupWith(l:List,s:Set[Int]) : Boolean = l match {
    case Nil() => true
    case Cons(h,l1) => !s.contains(h) && noDupWith(l1,Set(h) ++ s)
  }

  // l has no duplicates
  def noDup(l:List): Boolean = noDupWith(l,Set.empty[Int])

  // removing duplicates from l1 gives l2
  def removeDupGives(l1:List,l2:List) : Boolean =
    l2s(l1)==l2s(l2) && noDup(l2)

  def removeDupAnd(l:List,s0:Set[Int]) : List = (l match {
    case Nil() => Nil()
    case Cons(h,l1) => {
      if (s0.contains(h)) removeDupAnd(l1,s0)
      else Cons(h,removeDupAnd(l1,Set(h)++s0))
    }
  }) ensuring (res => noDupWith(res,s0) && l2s(l) ++ s0 == l2s(res) ++ s0)

  def removeDup(l:List) : List = ({
    removeDupAnd(l,Set.empty[Int])
  }) ensuring (res => removeDupGives(l,res))

  def revRemoveDupAnd(l:List,s0:Set[Int],l0:List) : List = ({
    require(l2s(l0).subsetOf(s0) && noDup(l0))
    l match {
      case Nil() => l0
      case Cons(h,l1) => {
    if (s0.contains(h)) revRemoveDupAnd(l1,s0,l0)
    else revRemoveDupAnd(l1,Set(h)++s0,Cons(h,l0))
      }
    }
  }) ensuring (res => noDupWith(res,s0) && l2s(l) ++l2s(l0) ++ s0 == l2s(res) ++ s0)

  def revRemoveDup(l:List) : List = ({
    revRemoveDupAnd(
      revRemoveDupAnd(l,Set.empty[Int],Nil()),
      Set.empty[Int],Nil())
  }) ensuring (res => removeDupGives(l,res))

  // tree of integers
  sealed abstract class Tree
  case class Node(left : Tree, value : Int, right : Tree) extends Tree
  case class Leaf() extends Tree

  // set of elements from t
  def t2s(t : Tree): Set[Int] = t match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => t2s(l) ++ Set(v) ++ t2s(r)
  }

  // list of t, in order, in from of l0
  def seqWith(t:Tree,l0:List) : List = (t match {
    case Leaf() => l0
    case Node(l, v, r) => seqWith(l,Cons(v,seqWith(r,l0)))
  }) ensuring (res => l2s(res) == t2s(t) ++ l2s(l0))

  // list of tree t
  def t2l(t:Tree) : List = seqWith(t,Nil())

  // list of elements of t, in order, without duplicates, in front of l0
  def seqNoDup(t:Tree,l0:List,s0:Set[Int]) : (List,Set[Int]) = ({
    require(l2s(l0).subsetOf(s0) && noDup(l0))
    t match {
      case Leaf() => (l0,s0)
      case Node(l, v, r) => {
    val (rl,rs) = seqNoDup(r,l0,s0)
    val (l1,s1) = if (rs.contains(v)) (rl,rs) else (Cons(v,rl),Set(v)++rs)
    seqNoDup(l,l1,s1)
      }
    }
  }) ensuring (res => {
    val (lres,sres) = res
    l2s(lres).subsetOf(sres) &&
    removeDupGives(t2l(t), lres)
  })

  // list of elements of t, without duplicates
  def t2lNoDup(t:Tree) : List = ({
    seqNoDup(t,Nil(),Set.empty[Int])._1
  }) ensuring (res => removeDupGives(t2l(t), res))
}
