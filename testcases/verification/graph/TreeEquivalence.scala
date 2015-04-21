import leon.annotation._
import leon.lang._

object TreeEquivalence {
  /** Graph representation.
   *
   * A graph has vertices 0, 1, ..., nVertices-1.
   *
   * Vertices is a singly linked list with length nVertices, corresponding in
   * order to the vertices 0, 1, ..., nVertices.
   * 
   * Each vertex has a list of edges, representing edges from that vertex to
   * the edge's toVertex field. This must not include the vertex itself. The
   * representation is for directed graphs.
   * 
   * Example:
   *
   * Graph(3,
   *   VertexItem(
   *     VertexItem(
   *       VertexItem(VertexEnd(),
   *         EdgeItem(EdgeItem(EdgeEnd(), 1), 0)),
   *       EdgeEnd()),
   *     EdgeItem(EdgeEnd(), 2))
   * )
   *
   * represents a graph with vertices 0, 1 and 2 with edges (2,0), (2,1) and (0,2).
   */
  case class Graph(nVertices : Int, vertices : Vertices)
  sealed abstract class Vertices
  case class VertexItem(next : Vertices, edges : Edges) extends Vertices
  case class VertexEnd() extends Vertices
  sealed abstract class Edges
  case class EdgeItem(next : Edges, toVertex : Int, weight : Int) extends Edges
  case class EdgeEnd() extends Edges


  /*
   -----------------------------------------------------------------------------
   TREE EQUIVALENCE TESTS
   -----------------------------------------------------------------------------
   */

  
  /*
   Try to prove that a spanning tree has (g.nVertices - 1) edges
   This is true for undirected graphs, but here we don't enforce the
   condition.
   
   Finds a counter-example sometimes after quite some time.
   */
  /*
  def treeEquivalence(g:Graph) : Boolean = {
    require(invariant(g) && isConnected(g) && g.nVertices > 0 && g.nVertices <=3)
    (!isSpanningTree(g) || ((getNumberOfEdges(g) == g.nVertices - 1)))
  } holds
  */
  
  
  /*
   Try to prove that every connected graph has (g.nVertices - 1) edges
   
   Finds counter example quickly (empty graph). No options
   */
  def connectedGraph(g:Graph) : Boolean = {
    require(invariant(g) && isConnected(g))
    (getNumberOfEdges(g) == g.nVertices - 1)
  } holds


  /*
   * - Trying to prove that every connected, non-empty graph has
   (g.nVertices - 1) edges
   * - Since we left out some isUndirected condtion it finds a counter example
   *   sometimes (depends on the upper bound of
   *   g.nVertices, the larger the more time it needs to find a
   *   counter example)
   */
  def nonEmptyConnectedGraph(g:Graph) : Boolean = {
    require(invariant(g) && isConnected(g) && g.nVertices > 0 &&
	    g.nVertices < 4)
    (getNumberOfEdges(g) == g.nVertices - 1)
  } holds

  
  /*
   -----------------------------------------------------------------------------
   GRAPH FUNCTIONS
   -----------------------------------------------------------------------------
   */
  
  /* Helper function (for conditions). */
  def lenVertexList(vertices : Vertices) : Int = vertices match {
    case VertexEnd() => 0
    case VertexItem(next, _) => 1+lenVertexList(next)
  }

  /* * Return true if and only if the graph representation is valid.
   *
   * Checks:
   *  nVertices >= 0
   *  length of vertex list is nVertices,
   *  there is no edge from a vertex to itself (no self-loops),
   *  there is not more than one edge from any vertex to any other,
   *  there are no edges to invalid vertices.
   * */
  def invariant(g : Graph) : Boolean = {
    
    def recEdges(edge : Edges, alreadyFound : Set[Int]) : Boolean = edge match {
      case EdgeEnd() => true
      case EdgeItem(next, toVertex, w) =>{
	0 <= toVertex && toVertex < g.nVertices &&
	!alreadyFound.contains(toVertex) &&
	recEdges(next, alreadyFound++Set(toVertex))
      }
    }
    
    def recVertices(i : Int, vertex : Vertices) : Boolean = vertex match {
      case VertexEnd() =>
	i == g.nVertices      // list should only be null if length is correct
      case VertexItem(next,edges) =>
	if (i >= g.nVertices)
          false
	else
          recEdges(edges, Set(i)) && recVertices(i+1, next)
    }
    
    g.nVertices >= 0 && recVertices(0, g.vertices)
  }

  
  /*
   * Returns the edges of a graph as a map 
   */
  def getEdges(g : Graph) : Map[(Int, Int), Int] = {
    require(invariant(g))
    
    def recEdges(from : Int, edge : Edges, acc : Map[(Int,Int), Int]) : Map[(Int, Int), Int] = edge match {
      case EdgeEnd() => acc
      case EdgeItem(next,toVertex,w) =>
	recEdges(from, next, acc.updated((from,toVertex), w))
    }
    
    def recVertices(i : Int, vertex : Vertices, acc : Map[(Int,Int), Int])
    : Map[(Int, Int), Int] = vertex match {
      case VertexEnd() =>  acc
      case VertexItem(next,edges) => {
	val a = recEdges(i, edges, acc)
	recVertices(i + 1, next, a)
      }
    }

    recVertices(0, g.vertices, Map.empty[(Int,Int), Int])
  }

  /*
   Counts the number of edges in a graph
   */
  def getNumberOfEdges(g : Graph) : Int = {
    require(invariant(g))

    def recEdges(from : Int, edge : Edges, acc : Int) : Int = edge
    match {
      case EdgeEnd() => acc
      case EdgeItem(next,toVertex,_) => recEdges(from, next, acc + 1)
    }
    
    def recVertices(i : Int, vertex : Vertices, acc : Int)
    : Int = vertex match {
      case VertexEnd () => acc
      case VertexItem(next,edges) => {
	val e = recEdges(i, edges, acc)
	recVertices(i + 1, next, e)
      }
    }

    recVertices(0, g.vertices, 0)
  }


  /*
   * Tests whether a given edge set forms a spanning tree using
   union - find
   */
  def isSpanningTree(g : Graph) : Boolean = {
    require(invariant(g))
    isConnected(g) && isAcyclic(g)
  }

  def isConnected(g : Graph) : Boolean = {
    require(invariant(g))
    isConnected(getEdges(g), g.nVertices)
  }

  def isConnected(edges : Map[(Int,Int), Int], nVertices : Int) :
  Boolean = {
    require(nVertices >= 0)
    val uf = calculateUF(edges, nVertices)._1

    val p = uFind(0, uf)
    var i = 1

    var ret = true
    while(i < nVertices && ret) {
      if(uFind(i, uf) != p)
	ret = false    // 0, i are not connected
      i += 1
    }

    ret
  }

  /*
   * Tests, whether g is cycle-free
   */
  def isAcyclic(g : Graph) : Boolean = {
    require(invariant(g))
    !calculateUF(getEdges(g),g.nVertices)._2
  }

  /*
   * Tests, whether the subgraph induced by edges is cycle-free.
   * If directed==true, the edge set is interpreted as directed edges
   * i.e. a->b and b->a are considered as two distinct edges.
   */
  def isAcyclic(edges : Map[(Int,Int), Int], nVertices : Int) : Boolean = {
    require(nVertices >= 0)
    !calculateUF(edges, nVertices)._2
  }


  /*
   * Does union-find on edgeSet.
   * Returns the union-find tree and a boolean set to true if a cycle was found
   */
  def calculateUF(edgeSet : Map[(Int,Int), Int], nVertices : Int) :
  (Map[Int, Int], Boolean)= {
    require(nVertices >= 0)
    
    var i = 0
    var uf = Map.empty[Int, Int]
    var cycle = false
    var edges = edgeSet
    while(i < nVertices) {
      var j = 0
      while(j < nVertices) {
	if(edges.isDefinedAt((i,j))) {
	  if(edges(i, j) != -1) {
	    val p1 = uFind(i, uf)
	    val p2 = uFind(j, uf)
	    if(p1 == p2)
	      cycle = true
	    else
	      uf = union(p1, p2, uf)

	    //"remove" twin edge
	    edges = edges.updated((j,i), -1)
	  }	   
	}
	j += 1
      }
      i += 1
    }

    (uf, cycle)
  }
  

  /* *************************************
   Union find
   *************************************** */
  def uFind(e : Int, s : Map[Int, Int]) : Int = {
    if(!s.isDefinedAt(e)) e
    else if(s(e) == e) e
    else uFind(s(e), s)
  }

  def union(e1 : Int, e2 : Int, s : Map[Int,Int]) : Map[Int, Int] = {
    // naive union
    val p1 = uFind(e1,s)
    val p2 = uFind(e2, s)
    
    if(p1 != p2)
      //naive union
      s.updated(p1, p2) //only union if theiy are really in different trees
    else
      s
  }
}
