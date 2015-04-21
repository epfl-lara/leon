import leon.annotation._
import leon.lang._

object Subgraph {
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
   SUBGRAPH TESTS
   -----------------------------------------------------------------------------
   */

  /*
   Empty graph is a subgraph of any other graph
   Works.
   */  
  def emptyGraph(g : Graph) : Boolean = {
    require(invariant(g))
    val empty = Graph(0, VertexEnd())
    isSubGraph(empty, g)
  } holds

  /*
   Graph with a single vertex is a subgraph of any other graph
   Finds counter example (empty graph) quickly
   */
  def singleGraphSubsetOfAnotherGraph(g : Graph) : Boolean = {
    require(invariant(g))
    val single = Graph(1, VertexItem(VertexEnd(), EdgeEnd()))
    isSubGraph(single, g)
  } holds

  /*
  // Leon times out
  def subGraphIsReflexive(g : Graph) : Boolean = {
    require(invariant(g) && g.nVertices <= 3)
    isSubGraph(g,g)
  } holds
  */

  /*
  // Leon times out
   def isSubGraphIsAntiSymmetric(g1 : Graph, g2 : Graph) : Boolean = {
    require(invariant(g1) && invariant(g2)) // && g1.nVertices <= 3 && g2.nVertices <= 3)
    !(isSubGraph(g1, g2) && isSubGraph(g2, g1)) || (g1 == g2)
  } holds
  */
  
  /*
   isSubGraphBogus does not check that g1 has equal or fewer
   vertices than g2 (i.e. that the vertex set of g1 is a subset of
   those of g2)
   
   Finds counter example often quickly, but needs sometimes more than 30s
   */
  def subGraphIsAntiSymmetricBogus(g1 : Graph, g2 : Graph) : Boolean = {
    require(invariant(g1) && invariant(g2))
    !(isSubGraphBogus(g1, g2) && isSubGraphBogus(g2, g1)) || (g1 == g2)
  } holds
   
  /*
   isSubGraphBogus2: The weights are ignored
   
   Leon times out.
   */
  /*
   def subGraphIsAntiSymmetricBogus2(g1 : Graph, g2 : Graph) : Boolean = {
   require(invariant(g1) && invariant(g2)) // && g1.nVertices <= 3 && g2.nVertices <= 3)
   !(isSubGraphBogus2(g1, g2) && isSubGraphBogus2(g2, g1)) || (g1 == g2)
   } holds
  */

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
   
   // Leon bug(?): cannot access g.nVertices from within this function:
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
   * Tests if g1 is a subgraph of g2.
   * We iterate over all edges in g1 and test if they also exist in g2
   */
  def isSubGraph(g1 : Graph, g2 : Graph) : Boolean = {
    require(invariant(g1) && invariant(g2))

    val edges2 = getEdges(g2)

    def recEdges(from : Int, edge : Edges, acc : Boolean) : Boolean = {
      if(!acc) false //fail fast
      else {
	edge match {
	  case EdgeEnd() => acc
	  case EdgeItem(next,toVertex,w) => {
	    if(edges2.isDefinedAt(from, toVertex)) {
	      if(edges2(from, toVertex) != w)
		false
	      else
		acc
	    }
	      else false
	  }
	}
      }
    }
    
    def recVertices(i : Int, vertex : Vertices, acc : Boolean) : Boolean = vertex match {
      case VertexEnd () => acc
      case VertexItem(next,edges) => {
	val b  = recEdges(i, edges, acc)
	recVertices(i + 1, next, b)
      }
    }

    if(g1.nVertices > g2.nVertices) // Vertex set needs to be a subset
      false
    else
      recVertices(0, g1.vertices, true)
  }

  /*
   Tests if g1 is a subgraph of g2.
   Bogus version 1: number of vertices needs to be taken in account
   */
  def isSubGraphBogus(g1 : Graph, g2 : Graph) : Boolean = {
    require(invariant(g1) && invariant(g2))

    val edges2 = getEdges(g2)

    def recEdges(from : Int, edge : Edges, acc : Boolean) : Boolean = edge match {
      case EdgeEnd() => acc
      case EdgeItem(next,toVertex,_) => acc && edges2.isDefinedAt(from, toVertex)
    }
    
    def recVertices(i : Int, vertex : Vertices, acc : Boolean) : Boolean = vertex match {
      case VertexEnd () => acc
      case VertexItem(next,edges) => {
	val b  = recEdges(i, edges, acc)
	recVertices(i + 1, next, b)
      }
    }

    recVertices(0, g1.vertices, true)
  }

  /*
   Bogus version 2: weights of edges also need to be considered
   */
  def isSubGraphBogus2(g1 : Graph, g2 : Graph) : Boolean = {
    require(invariant(g1) && invariant(g2))

    val edges2 = getEdges(g2)

    def recEdges(from : Int, edge : Edges, acc : Boolean) : Boolean = edge match {
      case EdgeEnd() => acc
      case EdgeItem(next,toVertex,_) => acc && edges2.isDefinedAt(from, toVertex)
    }
    
    def recVertices(i : Int, vertex : Vertices, acc : Boolean) : Boolean = vertex match {
      case VertexEnd () => acc
      case VertexItem(next,edges) => {
	val b  = recEdges(i, edges, acc)
	recVertices(i + 1, next, b)
      }
    }

    if(g1.nVertices > g2.nVertices) // Vertex set needs to be a subset
      false
    else
      recVertices(0, g1.vertices, true)
  }
}
