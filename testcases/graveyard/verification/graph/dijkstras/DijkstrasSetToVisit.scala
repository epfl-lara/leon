import leon.annotation._
import leon.lang._

/** Implementation of Dijkstra's algorithm. Maintains a list of visitable
 * vertices, and iterates over this, looking distances up in a map.
 */
object DijkstrasSetToVisit {
  /***************************************************************************
   * Graph representation and algorithms
   **************************************************************************/
  case class Graph(nVertices : Int, edges : Map[(Int,Int), Int])
  
  // TODO: disallow self edges?
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
        ret = if (g.edges.isDefinedAt((i,j))){
          if (g.edges((i,j)) >= 0) ret
          else false
        } else ret
        j += 1
      }
      i += 1
    }
    ret
  }
  
  
  /***************************************************************************
   * Dijkstra's algorithm
   **************************************************************************/
  
  /** Find the unvisited node with lowest distance.
   *
   * @param toVisit List of nodes to visit
   * @param distances Map of nodes to distances. Should be defined for all
   *  elements in toVisit.
   * @param best Best node, distance so far, or -1, Int.MaxValue
   * @return Best node, best distance, or best if no nodes.
   */
  def smallestUnvisited0( toVisit:Set[Int], distances:Map[Int,Int], best:(Int,Int) ) : (Int,Int) ={
    if (toVisit == Set.empty[Int])
      best
    else{
      val node = epsilon( (x:Int) => toVisit.contains(x) )
      val dist = distances(node)
      val next:(Int,Int) =
        if (dist < best._2) (node,dist)
      else best
      smallestUnvisited0(toVisit -- Set(node), distances, next)
    }
  }
  /** Find the unvisited node with lowest distance.
   *
   * @param toVisit List of nodes to visit
   * @param distances Map of nodes to distances. Should be defined for all
   *  elements in toVisit.
   * @return Best node, best distance, or (-1, Int.MaxValue) if no nodes.
   */
  def smallestUnvisited( toVisit:Set[Int], distances:Map[Int,Int] ) : (Int,Int) ={
    smallestUnvisited0(toVisit, distances, (-1, Int.MaxValue))
  } ensuring (ret => (ret._1== -1 && ret._2==Int.MaxValue) || (toVisit.contains(ret._1) && distances(ret._1) == ret._2))
  
  
  // common precondition: g is a valid graph and a and b are valid nodes
  def bounds(g : Graph, a : Int, b : Int) : Boolean =
    invariant(g) && 0 <= a && a < g.nVertices && 0 <= b && b < g.nVertices
  
  def min(a:Int, b:Int) = if (a<b) a else b
  // Generate map of "inf" distances for each node. "Inf" is Int.MaxValue.
  def infDistances(n:Int) : Map[Int,Int] ={
    if (n < 0) Map.empty[Int,Int]
    else infDistances(n-1).updated(n,Int.MaxValue)
  }
  
  // find the shortest path from a to b in g, and return its distance
  // return -1 if the two aren't connected
  def shortestPath(g : Graph, a : Int, b : Int) : Int = {
    require(bounds(g,a,b) && nonnegativeWeights(g))
    
    // We should always have at least some node if we haven't reached b (so
    // long as b is in the graph and connected to a).
    def spVisit (visited:Set[Int], toVisit:Set[Int], distances:Map[Int,Int]) : Int = {
      require(bounds(g,a,b) && toVisit.contains(b))
      
      val (node,dist) = smallestUnvisited(toVisit, distances)
      if (node == b || node < 0)
        dist
      else {
        var newVisitable = toVisit
        var newDistances = distances
        var n = 0
        
        (while (n < g.nVertices){
          if (n != node && !visited.contains(n) && g.edges.isDefinedAt((node,n))){
            newVisitable = newVisitable++Set(n)
            newDistances = newDistances.updated(n,
              min(newDistances(n), dist+g.edges((node,n))))
          }
          n = n + 1
        }) invariant(/*TODO: and that all elements in newVisitable are defined in newDistances*/ n >= 0 && n <= g.nVertices)
        
        spVisit(visited ++ Set(node), newVisitable, newDistances)
      }
    }
    
    // We start from a, which has distance 0. All other nodes are unreachable.
    spVisit(Set.empty, Set(a), infDistances(g.nVertices).updated(a,0))
  } // TODO ensuring (res => res >= -1 /*(if (isReachable(g,a,b)) res>=0 else res== -1)*/)
  
  def main(args: Array[String]) {
    val spanningTreeE = Map((0,1) -> 1, (0,2) -> 2, (2,3) -> 5, (0,3) -> 10, (3,2) -> 0)
    val spanningTree = Graph(4, spanningTreeE)
    val singleGraph = Graph(1, Map.empty)
    
    println(spanningTree)
    println("from 0 to 3 (should be 7): "+shortestPath(spanningTree,0,3))
    println("from 3 to 1 (no path): "+shortestPath(spanningTree,3,1))
  }
}
