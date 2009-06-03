/**
 * Example adapted from book "Purely Functional Data Structures"
 * by Chris Okasaki.
 */ 

package funpm.ds
   
sealed abstract case class Heap() { 
  
  /** mege the current heap <code>this</code> with the <code>that</code> 
   *  heap.
   */
  def merge(that: Heap): Heap = this match {
    case E => that
    case T(_,x,a1,b1) => that match {
      case E => this
      case T(_,y,_,_) if x.leq(y) =>
        a1.makeT(x,b1.merge(that))
      case T(_,y,a2,b2) if !x.leq(y) =>
        a2.makeT(y,merge(b2))
    }
  }
  
  /** helper function that calculates the rank of a <code>T</code> node
   *  and swaps its children if necessary.
   */ 
  def makeT(x: Elem, that: Heap): Heap = 
    if(rankk() >= that.rankk()) {
      T(that.rankk() + 1, x, this, that)
    } else {
      T(rankk() + 1, x, that, this)
    }

  /** find the rank of a heap */
  def rankk(): Int = this match {
    case E => 0
    case T(rank,_,_,_) => rank
  }
  
  /** insert an element in the current heap <code>this</code>*/
  def insert(x: Elem): Heap = merge(T(1,x,E,E))
  
  /** Find the smallest element of the current heap <code>this</code>. 
   *  Invariant on this data structure entails that the minimum is at the root.
   */ 
  def findMin: Elem = this match {
    case E => Predef.error(toString())
    case T(_,x,_,_) => x
  }
  
  /** Delete the smallest element of the current heap <code>this</code>.
   *  Invariant on this data structure entails that the minimum is at the root.
   */
  def deleteMin: Heap = this match {
    case E => Predef.error(toString())
    case T(_,_,a: Heap,b: Heap) => a.merge(b)
  }
   
}

case class T(val rank: Int, val el: Elem, val left: Heap,val right: Heap) extends Heap
case object E extends Heap


class Elem(val value: Int) {
  
  def leq(that: Elem): Boolean =
    /* postcondition this.value <= that.value
     */
    this.value <= that.value
}


//main
object LeftistHeap extends Application {
  assert(E.insert(new Elem(8))
       .insert(new Elem(5))
       .insert(new Elem(4))
       .insert(new Elem(7))
       .insert(new Elem(6)).
    findMin.value == 4)
}