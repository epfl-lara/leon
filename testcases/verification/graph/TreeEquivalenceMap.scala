import leon.annotation._
import leon.lang._

object TreeEquivalenceSet {
  /*
   -----------------------------------------------------------------------------
   TREE EQUIVALENCE TESTS ON SET REPRESENTATION
   -----------------------------------------------------------------------------
   */
  
  /*
   Try to prove that a spanning tree has (g.nVertices - 1) edges
   
   Leon loops
   */
  /*
  def treeEquivalence(g:Graph) : Boolean = {
    require(invariant(g) && isUndirected(g) && g.nVertices > 0 && g.nVertices <= 3)
    (!isSpanningTree(g) || ((getNumberOfEdges(g) == g.nVertices - 1)))
  } holds
  */
  
  /*
   Try to prove that every connected graph has (g.nVertices - 1) edges
   
   Finds counter example with out of range edges (--noLuckyTests)
   */
  def connectedGraph(g:Graph) : Boolean = {
    require(invariant(g) && isConnected(g) && isUndirected(g))
    (getNumberOfEdges(g) == g.nVertices - 1)
  } holds

  
  /*
   Trying to prove that every connected, non-empty graph has (g.nVertices - 1) edges
   
   Leon loops
   */
  /*
  def nonEmptyConnectedGraph(g:Graph) : Boolean = {
    require(invariant(g) && isConnected(g) && isUndirected(g) && g.nVertices > 0 &&
	    g.nVertices <= 3)
    (getNumberOfEdges(g) == g.nVertices - 1)
  } holds
  */
  
  /*
   -----------------------------------------------------------------------------
   GRAPH FUNCTIONS
   -----------------------------------------------------------------------------
   */

  case class Graph(nVertices : Int, edges : Map[(Int,Int), Int])

  def invariant(g : Graph) = {
    def noSelfLoops(i : Int) : Boolean = {
      if(i >= g.nVertices) true
      else if(g.edges.isDefinedAt(i,i))
	false
      else
	noSelfLoops(i+1)
    }
    
    g.nVertices >= 0 && noSelfLoops(0)
  }

  /**
   Tests, if g is undirected, that is if for every edge (i,j) there is
   also and edge (j,i)
   Ignoring weights for the moment
   */

  def isUndirected(g: Graph) : Boolean = {
    require(invariant(g))

    val edgeSet = g.edges
    var res = true
    var i = 0
    while(i < g.nVertices && res) {
      var j = 0
      while(j < g.nVertices && res) {
	res = !edgeSet.isDefinedAt(i,j) || edgeSet.isDefinedAt(j,i)
	
	//If weights should considered
	if(res && edgeSet.isDefinedAt(i,j))
	  res = edgeSet(i,j) == edgeSet(j,i)
	
	j += 1
      }
      i += 1
    }

    res
  }
  
  /*
   Leon doesn't support size operators, so we need to count edges explicitely...
   
   Note that the upper bound on x can not be proven using this graph
   representation since leon will then pick some out of range edges
   */
  def getNumberOfEdges(g : Graph) : Int = {
    require(invariant(g))

    var i = 0
    var cnt = 0
    (while(i < g.nVertices) {
      var j = 0
      (while(j < g.nVertices) {
	if(g.edges.isDefinedAt(i,j))
	  cnt += 1
	j += 1
      }) invariant(cnt >= 0) //&& cnt <= g.nVertices * g.nVertices)
      i += 1
    }) invariant(cnt >= 0)  //&& cnt  <= g.nVertices * g.nVertices)

    cnt
  } ensuring(x => x >= 0) //&& x  <= g.nVertices * g.nVertices)
  
  def isSpanningTree(g : Graph) : Boolean = {
    require(invariant(g) && isUndirected(g))
    isConnected(g) && isAcyclic(g.edges, g.nVertices)
  }

  def isConnected(g : Graph) :  Boolean = {
    require(g.nVertices >= 0 && isUndirected(g))
    val uf = calculateUF(g.edges, g.nVertices)._1

    val p = uFind(0, uf)
    var i = 1

    var ret = true
    while(i < g.nVertices && ret) {
      if(uFind(i, uf) != p)
	ret = false    // 0, i are not connected
      i += 1
    }

    ret
  }

  /*
   * Tests, whether the subgraph induced by edges is cycle-free.
   */
  def isAcyclic(edges : Map[(Int,Int), Int], nVertices : Int) : Boolean = {
    require(nVertices >= 0 && isUndirected(Graph(nVertices, edges)))
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
