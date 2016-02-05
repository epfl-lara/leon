import leon.annotation._
import leon.lang._

/** Implementation of Dijkstra's algorithm.
 *
 * Complexity is a bit beyond what Leon can handle. See individual tests on
 * SortedNDList.
 */
object DijkstrasSortedList {
  /***************************************************************************
   * Graph representation and algorithms
   **************************************************************************/
  case class Graph(nVertices : Int, edges : Map[(Int,Int), Int])

  // Disallow self edges? Not actually important since they can be ignored.
  def invariant(g : Graph) = g.nVertices >= 0

  // true if x & y have same number of nodes and y has all x's edges
  def isSubGraph(x : Graph, y : Graph) : Boolean = {
    require(invariant(x) && invariant(y))

    var ret : Boolean = (x.nVertices == y.nVertices)
    if (ret){
      var i = 0
      while(i<x.nVertices) {
        var j = 0;
        while(j < x.nVertices) {
          if (i != j)
            ret &&= !x.edges.isDefinedAt((i,j)) || y.edges.isDefinedAt((i,j))
          j += 1
        }
        i += 1
      }
    }
    ret
  }

  // true if every edge has a weight of at least 0
  def nonnegativeWeights(g : Graph) : Boolean = {
    require(invariant(g))

    var ret : Boolean = true
    var i = 0
    while(i<g.nVertices) {
      var j = 0;
      while(j < g.nVertices) {
        ret = if (i != j && g.edges.isDefinedAt((i,j))){
          if (g.edges((i,j)) >= 0) ret
          else false
        } else ret
        j += 1
      }
      i += 1
    }
    ret
  }

  // true if b is reachable from a
  def isReachable(g : Graph, a : Int, b : Int) : Boolean = {
    require(invariant(g) && a >= 0 && a < g.nVertices && b >= 0 && b < g.nVertices)

    //TODO
    false
  }


  /***************************************************************************
   * Sorted list representation and algorithims
   **************************************************************************/

  /** A list containing node, dist pairs.
   *
   * Sorted by distance, nearest first. Distance must be non-negative. Node
   * values must be unique and non-negative.
   */
  abstract class SortedNDList
  case class ListNode(node : Int, dist : Int, next : SortedNDList) extends SortedNDList
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


  /***************************************************************************
   * Dijkstra's algorithm
   **************************************************************************/

  def isNodeNotB(list : SortedNDList, b : Int) : Boolean =
    list match {
      case ListNode(n, _, _) => n!=b
      case ListEnd() => false
    }

  // common precondition: g is a valid graph and a and b are valid nodes
  def bounds(g : Graph, a : Int, b : Int) : Boolean =
    invariant(g) && 0 <= a && a < g.nVertices && 0 <= b && b < g.nVertices

  // find the shortest path from a to b in g, and return its distance
  // return -1 if the two aren't connected
  def shortestPath(g : Graph, a : Int, b : Int) : Int = {
    require(bounds(g,a,b) && nonnegativeWeights(g))

    // We should always have at least some node if we haven't reached b (so
    // long as b is in the graph and connected to a).
    @induct
    def spVisit (list : SortedNDList, visited : Set[Int]) : SortedNDList = {
      require(bounds(g,a,b) && (!visited.contains(b) || listContains(list,b)) && sndInvariant(list))
      /* TODO: also check that all list nodes are less than g.nVertices.
       * We should check same invariant at function exit. But there's no point:
       * it's too much for Leon to reason about at once!
       */

      list match {
        case ListNode(node, dist, next) if (node==b) =>
          list
        case ListNode(node, dist, next) =>
          var n = 0
          var tail : SortedNDList = next

          (while (n < g.nVertices){
            if (n != node && !visited.contains(n) && g.edges.isDefinedAt((node,n)))
              tail = updateDistInList(tail, n, dist+g.edges((node,n)))
            n = n + 1
          }) invariant(sndInvariant(list) && n >= 0 && n <= g.nVertices)

          spVisit (tail, visited ++ Set(node))
        case ListEnd() =>
          list
      }
    } ensuring(res => res match {
      case ListEnd() => !isReachable(g,a,b)
      case ListNode(node,_,_) => node==b
    })

    // We start from a, which has distance 0. All other nodes implicitly have
    // infinite distance.
    val startingList : SortedNDList = ListNode(a, 0, ListEnd())
    spVisit(startingList, Set.empty) match {
      case ListNode(n, d, _) =>
        //assert(n==b)
        if (n != b)
          -2    // Leon should prove this doesn't happen — what a way to do assert(false)
        else
          d
      case ListEnd() =>
        -1
    }
  } ensuring (res => res >= -1 /*(if (isReachable(g,a,b)) res>=0 else res== -1)*/)

  @ignore
  def main(args: Array[String]) {
    val spanningTreeE = Map((0,1) -> 1, (0,2) -> 2, (2,3) -> 5, (0,3) -> 10, (3,2) -> 0)
    val spanningTree = Graph(4, spanningTreeE)
    val singleGraph = Graph(1, Map.empty)

    println(spanningTree)
    println("from 0 to 3 (should be 7): "+shortestPath(spanningTree,0,3))
    println("from 3 to 1 (no path): "+shortestPath(spanningTree,3,1))
  }
}
