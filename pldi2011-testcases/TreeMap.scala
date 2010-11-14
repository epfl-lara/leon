import scala.collection.immutable.Set
import funcheck.Utils._

object TreeMap {
  sealed abstract class TreeMap
  case class Empty() extends TreeMap
  case class Node(key: Int, datum: Int, left: TreeMap, right: TreeMap, height: Int) extends TreeMap

  sealed abstract class Tuple
  case class Triple(key: Int, datum: Int, tree: TreeMap) extends Tuple

  sealed abstract class IntList
  case class Cons(head: Int, tail: IntList) extends IntList
  case class Nil() extends IntList

  def main(args : Array[String]) : Unit = {
    val l =  Node(11, 12, Empty(), Node(13, 14, Node(36, 37, Empty(), Empty(), 38), Empty(), 5920), 5922)
    val r = Node(7, 8, Node(9, 10, Node(41, 42, Empty(), Empty(), 43), Empty(), 7719), Node(26, 27, Empty(), Empty(), 4680), 5921)

    val d = 4
    val x = 3

    println(balance(x, d, l, r))
  }

  def mmax(i: Int, j: Int) : Int = if(i >= j) i else j

  // checks that the height field is set properly.
  def nodeHeightsAreCorrect(tm: TreeMap) : Boolean = (tm match {
    case Empty() => true
    case n @ Node(_, _, l, r, h) => h == realHeight(n) && nodeHeightsAreCorrect(l) && nodeHeightsAreCorrect(r)
  }) ensuring(res => !res || (height(tm) == realHeight(tm)) )

  // measures "real height"
  def realHeight(tm: TreeMap) : Int = (tm match {
    case Empty() => 0
    case Node(_, _, l, r, _) => mmax(realHeight(l), realHeight(r)) + 1
  }) ensuring(_ >= 0)

  def height(tm: TreeMap): Int = (tm match {
    case Empty() => 0
    case Node(_,_,_,_,h) => h
  })

  /*
  def invariant0(tm : TreeMap) : Boolean = {
    require(nodeHeightsAreCorrect(tm))
    height(tm) == realHeight(tm)
  } holds

  def invariant1(tm: TreeMap): Boolean = {
    require((tm match {
      case Empty() => true
      case Node(_,_,l,r,_) => nodeHeightsAreCorrect(l) && nodeHeightsAreCorrect(r)
    }) && nodeHeightsAreCorrect(tm))
    tm match {
      case Empty() => true
      case Node(_,_,l,r,h) => h == mmax(height(l), height(r)) + 1
    }
  } // holds

  def invariant2(tm: TreeMap): Boolean = {
    require(nodeHeightsAreCorrect(tm))
    tm match {
      case Empty() => true
      case Node(_,_,l,r,_) => 
        val h = height(tm)
        h > height(l) && h > height(r) // && invariant2(l) && invariant2(r)
    }
  } // holds
  */

  def setOf(tm: TreeMap): Set[Int] = tm match {
    case Empty() => Set.empty
    case Node(d, _, l, r, _) => Set(d) ++ setOf(l) ++ setOf(r)
  }

  def create(k: Int, d: Int, l: TreeMap, r: TreeMap): TreeMap = {
    require(nodeHeightsAreCorrect(l) && nodeHeightsAreCorrect(r) && isBalanced(l) && isBalanced(r) &&
      height(l) - height(r) <= 2 && height(r) - height(l) <= 2)
    val hl = height(l)
    val hr = height(r)
    Node(k, d, l, r, mmax(hl, hr) + 1)
  } ensuring(res => setOf(res) == Set(k) ++ setOf(l) ++ setOf(r) && isBalanced(res))

  def balance(x: Int, d: Int, l: TreeMap, r: TreeMap): TreeMap = {
    require(
      nodeHeightsAreCorrect(l) && nodeHeightsAreCorrect(r) && isBalanced(l) && isBalanced(r) &&
      height(l) - height(r) <= 3 && height(r) - height(l) <= 3 &&
      (r match {
        case Empty() => false
        case Node(_, _, Empty(), _, _) => false
        case _ => true
      }) &&
      (l match {
        case Empty() => false
        case Node(_, _, _, Empty(), _) => false
        case _ => true
      })
    )

    val hl = height(l)
    val hr = height(r)
    if (hr > hl + 2) {
      r match {
        case Node(rv, rd, rl, rr, h) =>
          if (height(rr) >= height(rl)) {
            create(rv, rd, create(x, d, l, rl), rr)
          } else {
            rl match {
              case Node(rlv, rld, rll, rlr, h) => create(rlv, rld, create(x, d, l, rll), create(rv, rd, rlr, rr))
            }
          }
      }
    } else if (hl > hr + 2) {
      l match {
        case Node(lv, ld, ll, lr, h) =>
          if (height(ll) >= height(lr)) {
            create(lv, ld, ll, create(x, d, lr, r))
          } else {
            lr match {
              case Node(lrv, lrd, lrl, lrr, h) => create(lrv, lrd, create(lv, ld, ll, lrl), create(x, d, lrr, r))
            }
          }
      }
    } else
      Node(x, d, l, r, if(hl >= hr) hl + 1 else hr + 1)
  } ensuring(isBalanced(_))

  def add(x: Int, data: Int, tm: TreeMap): TreeMap = {
    require(isBalanced(tm) && nodeHeightsAreCorrect(tm))
    tm match {
      case Empty() => Node(x, data, Empty(), Empty(), 1)
      case Node(v, d, l, r, h) =>
        if (x == v)
          Node(x, data, l, r, h)
        else if (x < v)
          balance(v, d, add(x, data, l), r)
        else
          balance(v, d, l, add(x, data, r))
    }
  } ensuring(isBalanced(_))

  def removeMinBinding(t: TreeMap): Triple = {
    require(isBalanced(t) && (t match {
      case Empty() => false
      case _ => true
    }))
    t match {
      case Node(x, d, l, r, h) =>
        l match {
          case Empty() => Triple(x, d, r)
          case Node(_,_,ll, lr, h2) =>
            val triple = removeMinBinding(l)
            Triple(triple.key, triple.datum, balance(x, d, triple.tree, r))
        }
    }
  } ensuring(res => isBalanced(res.tree))

  // m is not used here!
  def merge(m: Int, t1: TreeMap, t2: TreeMap): TreeMap = {
    require(isBalanced(t1) && isBalanced(t2))
    t1 match {
      case Empty() => t2
      case Node(_, _, ll, lr, h1) =>
        t2 match {
          case Empty() => t1
          case Node(r, _, rl, rr, h2) =>
            val triple = removeMinBinding(t2)
            balance(triple.key, triple.datum, t1, triple.tree)
        }
    }
  } ensuring(isBalanced(_))

  def remove(x: Int, t: TreeMap): TreeMap = {
    require(isBalanced(t))
    t match {
      case Empty() => Empty()
      case Node(v, d, l, r, h) =>
        if (x == v)
          merge(x, l, r)
        else if (x < v)
          balance(v, d, remove(x, l), r)
        else
          balance(v, d, l, remove(x, r))
    }
  } ensuring(isBalanced(_))

  def find(t: TreeMap, x: Int): Int = {
    require(t match {
      case Empty() => false
      case _ => true
    })
    t match {
      case Node(d, _, l, r, _) =>
        if (x == d) 
          d
        else if (x < d)
          find(l, x)
        else
          find(r, x)
    }
  }

  // let us specialize iter for the condition k < v
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

  // We have a variant of AVL trees where the heights of the subtrees differ at
  // most by 2
  def isBalanced(t: TreeMap): Boolean = t match {
    case Empty() => true
    case Node(_, _, l, r, _) => (height(l) - height(r) <= 2 && height(r) - height(l) <= 2) && isBalanced(l) && isBalanced(r)
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
