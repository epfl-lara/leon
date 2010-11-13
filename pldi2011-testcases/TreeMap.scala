import scala.collection.immutable.Set

object TreeMap {
  sealed abstract class TreeMap
  case class Empty() extends TreeMap
  case class Node(key: Int, datum: Int, left: TreeMap, right: TreeMap, height: Int) extends TreeMap

  sealed abstract class Tuple
  case class Triple(key: Int, datum: Int, tree: TreeMap) extends Tuple

  sealed abstract class IntList
  case class Cons(head: Int, tail: IntList) extends IntList
  case class Nil() extends IntList

  def height(tm: TreeMap): Int = tm match {
    case Empty() => 0
    case Node(_,_,_,_,h) => h
  }

  def setOf(tm: TreeMap): Set[Int] = tm match {
    case Empty() => Set.empty
    case Node(d, _, l, r, _) => Set(d) ++ setOf(l) ++ setOf(r)
  }

  def create(k: Int, d: Int, l: TreeMap, r: TreeMap): TreeMap = {
    val hl = height(l)
    val hr = height(r)
    Node(k, d, l, r, if (hl >= hr) hl + 1 else hr + 1)
  }

  def balance(x: Int, d: Int, l: TreeMap, r: TreeMap): TreeMap = {
    val hl = height(l)
    val hr = height(r)
    if (hr > hl + 2) {
      r match {
        case Empty() => error("invalid arg")
        case Node(rv, rd, rl, rr, h) =>
          if (height(rr) >= height(rl)) {
            create(rv, rd, create(x, d, l, rl), rr)
          } else {
            rl match {
              case Empty() => error("invalid arg")
              case Node(rlv, rld, rll, rlr, h) =>
                create(rlv, rld, create(x, d, l, rll), create(rv, rd, rlr, rr))
            }
          }
      }
    } else if (hl > hr + 2) {
      l match {
        case Empty() => error("invalid arg")
        case Node(lv, ld, ll, lr, h) =>
          if (height(ll) >= height(lr)) {
            create(lv, ld, ll, create(x, d, lr, r))
          } else {
            lr match {
              case Empty() => error("invalid arg")
              case Node(lrv, lrd, lrl, lrr, h) =>
                create(lrv, lrd, create(lv, ld, ll, lrl), create(x, d, lrr, r))
            }
          }
      }
    } else
      Node(x, d, l, r, if(hl >= hr) hl + 1 else hr + 1)
  } ensuring(isBalanced(_))

  def add(x: Int, data: Int, tm: TreeMap): TreeMap = tm match {
    case Empty() => Node(x, data, Empty(), Empty(), 1)
    case Node(v, d, l, r, h) =>
      if (x == v)
        Node(x, data, l, r, h)
      else if (x < v)
        balance(v, d, add(x, data, l), r)
      else
        balance(v, d, l, add(x, data, r))
  }

  def removeMinBinding(t: TreeMap): Triple = t match {
    case Empty() => error("invalid arg")
    case Node(x, d, l, r, h) =>
      l match {
        case Empty() => Triple(x, d, r)
        case Node(_,_,ll, lr, h2) =>
          val triple = removeMinBinding(l)
          Triple(triple.key, triple.datum, balance(x, d, triple.tree, r))
      }
  }

  // m is not used here!
  def merge(m: Int, t1: TreeMap, t2: TreeMap): TreeMap = t1 match {
    case Empty() => t2
    case Node(_, _, ll, lr, h1) =>
      t2 match {
        case Empty() => t1
        case Node(r, _, rl, rr, h2) =>
          val triple = removeMinBinding(t2)
          balance(triple.key, triple.datum, t1, triple.tree)
      }
  }

  def remove(x: Int, t: TreeMap): TreeMap = t match {
    case Empty() => Empty()
    case Node(v, d, l, r, h) =>
      if (x == v)
        merge(x, l, r)
      else if (x < v)
        balance(v, d, remove(x, l), r)
      else
        balance(v, d, l, remove(x, r))
  }

  def find(t: TreeMap, x: Int): Int = t match {
    case Empty() => error("invalid arg")
    case Node(d, _, l, r, _) =>
      if (x == d) 
        d
      else if (x < d)
        find(l, x)
      else
        find(r, x)
  }

  // iter takes a function...

  // let us specialize it for the condition k < v
  def iter1(t: TreeMap, v: Int): Boolean = t match {
    case Empty() => true
    case Node(k, d, l, r, _) =>
      k < v && iter1(l, v) && iter1(r, v)
  }

  // also for the condition v < k
  def iter2(t: TreeMap, v: Int): Boolean = t match {
    case Empty() => true
    case Node(k, d, l, r, _) =>
      v < k && iter2(l, v) && iter2(r, v)
  }

  def checkBST(t: TreeMap): Boolean = t match {
    case Empty() => true
    case Node(v, _, l, r, _) =>
      iter1(l, v) && iter2(r, v) && checkBST(l) && checkBST(r)
  }

  def isBalanced(t: TreeMap): Boolean = t match {
    case Empty() => true
    case Node(_, _, l, r, _) =>
      height(l) - height(r) < 2 && height(r) - height(l) < 2 && isBalanced(l) && isBalanced(r)
  }

  /** list conversion **/

  def append(k: Int, xs: IntList, ys: IntList): IntList = xs match {
    case Nil() => Cons(k, ys)
    case Cons(x, xss) => Cons(x, append(k, xss, ys))
  }

  def toList(t: TreeMap): IntList = t match {
    case Empty() => Nil()
    case Node(v, _, l, r, _) =>
      val ls = toList(l)
      val rs = toList(r)
      append(v, ls, rs)
  }

  def isSorted(l: IntList): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x1, Cons(x2, xs)) => x1 <= x2 && isSorted(Cons(x2, xs))
  }

}
