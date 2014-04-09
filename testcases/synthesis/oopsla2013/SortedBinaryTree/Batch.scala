import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object BinaryTree {
  sealed abstract class Tree
  case class Node(left : Tree, value : Int, right : Tree) extends Tree
  case object Leaf extends Tree

  def content(t : Tree): Set[Int] = t match {
    case Leaf => Set.empty[Int]
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
  }
  
  sealed abstract class OptPair
  case class Pair(v1 : Int, v2 : Int) extends OptPair
  case object NoPair extends OptPair
  
  def isSortedX(t : Tree) : (Boolean, OptPair) = (t match {
    case Leaf                => (true, NoPair)
    case Node(Leaf, v, Leaf) => (true, Pair(v, v))
    case Node(Node(_, lv, _), v, _) if lv >= v => (false, NoPair)
    case Node(_, v, Node(_, rv, _)) if rv <= v => (false, NoPair)
      
    case Node(l, v, r) =>
      val (ls,lb) = isSortedX(l)
               
      val (lOK,newMin) = lb match {
        case NoPair => (ls, v)
        case Pair(ll, lh) => (ls && lh < v, ll)
      }
         
      if(lOK) {
        val (rs,rb) = isSortedX(r)
        val (rOK,newMax) = rb match {
          case NoPair => (rs, v)
          case Pair(rl, rh) => (rs && v < rl, rh)
        }

        if(rOK) {
          (true, Pair(newMin, newMax))
        } else {
          (false, NoPair)
        }
      } else {
        (false, NoPair)
      }
  }) ensuring((res : (Boolean,OptPair)) => res match {
    case (s, Pair(l,u)) => s && (l <= u)
    case _ => true  
  })

  def isSorted(t: Tree): Boolean = isSortedX(t)._1

  def deleteSynth(in : Tree, v : Int) = choose {
    (out : Tree) => content(out) == (content(in) -- Set(v))
  }

  // def insertImpl(t : Tree, x : Int) : Tree = {
  //   require(isSorted(t))
  //   t match {
  //    case Leaf => Node(Leaf, x, Leaf)
  //    case Node(l, v, r) if v == x => Node(l, v, r)
  //    case Node(l, v, r) if x < v  => Node(insertImpl(l, x), v, r)
  //    case Node(l, v, r) if v < x  => Node(l, v, insertImpl(r, x))
  //   }
  // } ensuring(isSorted(_))
 
  def insertSynth(in : Tree, v : Int) = choose {
    (out : Tree) => content(out) == (content(in) ++ Set(v))
  }

  def insertSortedSynth(in : Tree, v : Int) = choose {
    (out : Tree) => isSorted(in) && (content(out) == (content(in) ++ Set(v))) && isSorted(out)
  }

  def deleteSortedSynth(in : Tree, v : Int) = choose {
    (out : Tree) => isSorted(in) && (content(out) == (content(in) -- Set(v))) && isSorted(out)
  }
}
