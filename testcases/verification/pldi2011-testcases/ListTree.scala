import leon.lang._

object ListTree { 
  /* Trees holding integers and internal lists */
  sealed abstract class IntTreeList
  case class Cons(head: IntTree, tail: IntTreeList) extends IntTreeList
  case class Nil() extends IntTreeList

  sealed abstract class IntTree
  case class Leaf(value: Int) extends IntTree
  case class Node(list: IntTreeList) extends IntTree

  /* Trees holding pairs of integers and internal lists */
  sealed abstract class IntIntTreeList
  case class Cons2(head: IntIntTree, tail: IntIntTreeList) extends IntIntTreeList
  case class Nil2() extends IntIntTreeList

  sealed abstract class IntIntTree
  case class Leaf2(value: IntIntPair) extends IntIntTree
  case class Node2(list: IntIntTreeList) extends IntIntTree

  /* Various tuples that are needed below */
  sealed abstract class Tuple
  case class TreeIntPair(tree: IntTree, int: Int) extends Tuple
  case class IntIntPair(fst: Int, snd: Int) extends Tuple
  
  // we are going to specialize fold, map, iter, and build2 for their uses

  // we specialize iter for v <= x
  def iter1(t: IntTree, v: Int): Boolean = t match {
    case Leaf(x) => v <= x
    case Node(ts) => iter1list(ts, v)
  }
  // specialize for iter1
  def iter1list(l: IntTreeList, v: Int): Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => iter1(x, v) && iter1list(xs, v)
  }

  // specialize iter for (a, b) =>  k <= a && k <= b
  def iter2(t: IntIntTree, k: Int): Boolean = t match {
    case Leaf2(IntIntPair(a, b)) => k <= a && k <= b
    case Node2(ts) => iter2list(ts, k)
  }

  // specialize for iter2
  def iter2list(ts: IntIntTreeList, k: Int): Boolean = ts match {
    case Nil2() => true
    case Cons2(x, xs) => iter2(x, k) && iter2list(xs, k)
  }

  // specialize build2 for f(x) = x + 1
  def build2(b: Int, d: Int): TreeIntPair = {
    if (d <= 0)
      TreeIntPair(Leaf(b), b + 1)
    else {
      val p1 = build2(b, d-1)
      val p2 = build2(p1.int, d-1)
      TreeIntPair(Node(Cons(p1.tree, Cons(p2.tree, Nil()))), p2.int)
    }
  }

  // specialize fold for function +
  def fold1(b: Int, t: IntTree): Int = t match {
    case Leaf(x) => x + b
    case Node(ts) => foldLeft1(b, ts)
  }

  // specialize for the fold1 method above
  def foldLeft1(b: Int, ts: IntTreeList): Int = ts match {
    case Nil() => b
    case Cons(x, xs) => foldLeft1(fold1(b, x), xs)
  }

  // specialize fold for function lub
  def fold2(b: IntIntPair, t: IntIntTree): IntIntPair = t match {
    case Leaf2(x) => lub(b, x)
    case Node2(ts) => foldLeft2(b, ts)
  }

  // specialize foldLeft for the fold2 function
  def foldLeft2(b: IntIntPair, ts: IntIntTreeList): IntIntPair = ts match {
    case Nil2() => b
    case Cons2(x, xs) => foldLeft2(fold2(b, x), xs)
  }

  // specialize map for demo2, with function x => (x, 2*x + 1)
  def map1(t: IntTree): IntIntTree = t match {
    case Leaf(x) => Leaf2(IntIntPair(x, 2*x + 1))
    case Node(ts) => Node2(map1list(ts))
  }

  // specialize for demo2, with function map1 above
  def map1list(ts: IntTreeList): IntIntTreeList = ts match {
    case Nil() => Nil2()
    case Cons(x, xs) => Cons2(map1(x), map1list(xs))
  }

  /****/

  def make(n: Int, v: Int): IntTree = {
    if (n <= 0)
      Leaf(v)
    else {
      val t1 = make(n-1, v+1)
      val t2 = make(n-2, v+2)
      val t3 = make(n-3, v+3)
      Node(Cons(t1, Cons(t2, Cons(t3, Nil()))))
    }
  } ensuring(res => iter1(res, v)) /* all elements larger than v (demo0 test) */
  
  /****/

  def demo1(d: Int, k: Int): Int = {
    require(k >= 0)
    val t = build2(k+1, d).tree
    fold1(k, t)
  } ensuring(_ >= k)

  /****/

  def mmin(x: Int, y: Int): Int = if (x <= y) x else y
  def mmax(x: Int, y: Int): Int = if (x <= y) y else x

  def lub(p1: IntIntPair, p2: IntIntPair): IntIntPair = {
    val newFst = mmin(p1.fst, p2.fst)
    val newSnd = mmax(p1.snd, p2.snd)
    IntIntPair(newFst, newSnd)
  }

  def demo2a(d: Int, k: Int): IntIntTree = {
    require(k >= 0)
    val t = build2(k, d).tree
    map1(t)
  } ensuring(iter2(_, k))

  def demo2b(d: Int, k: Int): IntIntPair = {
    require(k >= 0)
    val t = build2(k, d).tree
    val t1 = map1(t)
    fold2(IntIntPair(k, k), t1)
  } ensuring(res => res.fst <= res.snd)
}
