import leon.invariant._
import leon.instrumentation._
import leon.math._

/**
 * created by manos and modified by ravi.
 * BST property cannot be verified
 */
object AVLTree  {
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left : Tree, value : BigInt, right: Tree, rank : BigInt) extends Tree

  sealed abstract class OptionInt
  case class None() extends OptionInt
  case class Some(i: BigInt) extends OptionInt

  //def min(i1:BigInt, i2:BigInt) : BigInt = if (i1<=i2) i1 else i2
  //def max(i1:BigInt, i2:BigInt) : BigInt = if (i1>=i2) i1 else i2

  /*def twopower(x: BigInt) : BigInt = {
    //require(x >= 0)
    if(x < 1) 1
    else
      3/2 * twopower(x - 1)
  } ensuring(res => res >= 1 template((a) => a <= 0))*/

  def rank(t: Tree) : BigInt = {
    t match {
      case Leaf() => 0
      case Node(_,_,_,rk) => rk
    }
  } //ensuring(res => res >= 0)

  def height(t: Tree): BigInt = {
    t match {
      case Leaf() => 0
      case Node(l, x, r, _) => {
        val hl = height(l)
        val hr = height(r)
        max(hl,hr) + 1
      }
    }
  }

  def size(t: Tree): BigInt = {
    //require(isAVL(t))
    (t match {
      case Leaf() => 0
      case Node(l, _, r,_) => size(l) + 1 + size(r)
    })

  }
  //ensuring (res => true template((a,b) => height(t) <= a*res + b))

  def rankHeight(t: Tree) : Boolean = t match {
    case Leaf() => true
    case Node(l,_,r,rk) => rankHeight(l) && rankHeight(r) && rk == height(t)
  }

  def balanceFactor(t : Tree) : BigInt = {
    t match{
      case Leaf() => 0
      case Node(l, _, r, _) => rank(l) - rank(r)
    }
  }

  /*def isAVL(t:Tree) : Boolean = {
    t match {
        case Leaf() => true
        case Node(l,_,r,rk) =>  isAVL(l) && isAVL(r) && balanceFactor(t) >= -1 && balanceFactor(t) <= 1 && rankHeight(t) //isBST(t) &&
      }
  }*/

  def unbalancedInsert(t: Tree, e : BigInt) : Tree = {
    t match {
      case Leaf() => Node(Leaf(), e, Leaf(), 1)
      case Node(l,v,r,h) =>
             if (e == v) t
        else if (e <  v){
          val newl = avlInsert(l,e)
          Node(newl, v, r, max(rank(newl), rank(r)) + 1)
        }
        else {
          val newr = avlInsert(r,e)
          Node(l, v, newr, max(rank(l), rank(newr)) + 1)
        }
    }
  }

  def avlInsert(t: Tree, e : BigInt) : Tree = {

    balance(unbalancedInsert(t,e))

  } ensuring(res => tmpl((a,b) => time <= a*height(t) + b))
  //ensuring(res => time <= 276*height(t) + 38)
  //minbound: ensuring(res => time <= 138*height(t) + 19)

  def deletemax(t: Tree): (Tree, OptionInt) = {

    t match {
      case Node(Leaf(), v, Leaf(), _) => (Leaf(), Some(v))
      case Node(l, v, Leaf(), _) => {
        val (newl, opt) =  deletemax(l)
        opt match {
          case None() => (t, None())
          case Some(lmax) => {
            val newt = balance(Node(newl, lmax, Leaf(), rank(newl) + 1))
            (newt, Some(v))
          }
        }
      }
      case Node(_, _, r, _) => deletemax(r)
      case _ => (t, None())
    }
  } ensuring(res => tmpl((a,b) => time <= a*height(t) + b))

  def unbalancedDelete(t: Tree, e: BigInt): Tree = {
    t match {
      case Leaf() => Leaf() //not found case
      case Node(l, v, r, h) =>
        if (e == v) {
          if (l == Leaf()) r
          else if(r == Leaf()) l
          else {
            val (newl, opt) = deletemax(l)
            opt match {
              case None() => t
              case Some(newe) => {
                Node(newl, newe, r, max(rank(newl), rank(r)) + 1)
              }
            }
          }
        } else if (e < v) {
          val newl = avlDelete(l, e)
          Node(newl, v, r, max(rank(newl), rank(r)) + 1)
        } else {
          val newr = avlDelete(r, e)
          Node(l, v, newr, max(rank(l), rank(newr)) + 1)
        }
    }
  }

  def avlDelete(t: Tree, e: BigInt): Tree = {

    balance(unbalancedDelete(t, e))

  } ensuring(res => tmpl((a,b) => time <= a*height(t) + b))

  def balance(t:Tree) : Tree = {
    t match {
      case Leaf() => Leaf() // impossible...
      case Node(l, v, r, h) =>
        val bfactor = balanceFactor(t)
        // at this point, the tree is unbalanced
        if(bfactor > 1 ) { // left-heavy
          val newL =
            if (balanceFactor(l) < 0) { // l is right heavy
              rotateLeft(l)
            }
            else l
          rotateRight(Node(newL,v,r, max(rank(newL), rank(r)) + 1))
        }
        else if(bfactor < -1) {
          val newR =
            if (balanceFactor(r) > 0) { // r is left heavy
              rotateRight(r)
            }
            else r
          rotateLeft(Node(l,v,newR, max(rank(newR), rank(l)) + 1))
        } else t
      }
  }

  def rotateRight(t:Tree) = {
    t match {
      case Node(Node(ll, vl, rl, _),v,r, _) =>

        val hr = max(rank(rl),rank(r)) + 1
        Node(ll, vl, Node(rl,v,r,hr), max(rank(ll),hr) + 1)

      case _ => t // this should not happen
  } }


  def rotateLeft(t:Tree) =  {
    t match {
      case Node(l, v, Node(lr,vr,rr,_), _) =>

        val hl = max(rank(l),rank(lr)) + 1
        Node(Node(l,v,lr,hl), vr, rr, max(hl, rank(rr)) + 1)
      case _ => t // this should not happen
  } }
}

