import leon.annotation._
import leon.lang._

/** Tests for SortedNDList
 */
object SortedNDList {
  /** A list containing node, dist pairs.
   *
   * Sorted by distance, nearest first. Distance must be non-negative. Node
   * values must be unique and non-negative.
   */
  abstract class SortedNDList
  case class ListNode(node: Int, dist: Int, next: SortedNDList) extends SortedNDList
  case class ListEnd() extends SortedNDList
  
  /** List invariant (see description above) */
  @induct
  def sndInvariant(list : SortedNDList) : Boolean = {
    // Most conditions are commented out. Leon cannot even check adding or
    // removing an element satisfies the invariant in this case!
    def invRec(list : SortedNDList/*, elts : Set[Int], minDist : Int, len : Int*/) : Boolean =
      list match {
        case ListNode(n,d,next) =>
          if (d >= 0/*minDist*/ && n >= 0 /*&& !elts.contains(n)*/)
            invRec(next/*,elts++Set(n),d, len + 1*/)
          else
            false
        case ListEnd() => true //len <= 3
      }
    
    invRec(list/*, Set.empty, 0, 0*/)
  }
  
  /** Simple test function: does adding an element at the start of the list
   * maintain the invariant? */
  @induct def addStart(list : SortedNDList, node:Int, dist:Int) : SortedNDList ={
    require (sndInvariant(list) && node>=0 && dist>=0)
    ListNode(node,dist,list)
  } ensuring(sndInvariant(_))   // Leon cannot verify this even when all the invariant does is check that node and dist are non-negative!
  
  /* Further tests fail, if run.
  
  /** Look for node in list and remove, if it exists. */
  @induct
  def removeFromList(list : SortedNDList, node : Int) : SortedNDList ={
    // something about this times out
    require(sndInvariant(list))
    
    //println("removeFromList: "+list)
    
    list match  {
      case ListNode(n,d,next) =>
        if (n == node)
          // drop current node and continue search:
          removeFromList(next, node)
        else
          ListNode(n,d,removeFromList(next, node))
      case ListEnd() => list
    }
  } ensuring(sndInvariant(_))   // something about this generates an error: is the precondition not checked for _all_ elements or something?
  
  /** Return true if list contains node */
  @induct
  def listContains(list : SortedNDList, node : Int) : Boolean ={
    // something to do with this times out
    require(sndInvariant(list))
    list match {
      case ListNode(n,d,next) =>
        if (node == n) true
        else listContains(next, node)
      case ListEnd() => false
    }
  }
  
  /** Add a new node to the list, such that list remains sorted by distance.
   * Assume node is not already in list. */
  @induct
  def addSorted(list : SortedNDList, node : Int, dist : Int) : SortedNDList = {
    // something to do with this times out
    require(sndInvariant(list) && !listContains(list, node) && node >= 0 && dist >= 0)
    
    list match {
      case ListNode(n,d,next) =>
        if (d > dist)        // insert here
          ListNode(node, dist, list)
        else
          ListNode(n,d, addSorted(next, node, dist))
      case ListEnd() => // insert at end
        ListNode(node, dist, list)
    }
  } ensuring (sndInvariant(_))  // something to do with this times out
  
  /** Update node with distance minimum of dist and current value. Add if not
   * in list, and maintain sorted order. */
  @induct
  def updateDistInList(list : SortedNDList, node : Int, dist : Int) : SortedNDList = {
    require(sndInvariant(list) && node >= 0 && dist >= 0)
    
    val listRemoved = removeFromList(list, node)
    addSorted(listRemoved, node, dist)
  } ensuring(sndInvariant(_))
  */
}
