import leon.annotation._
import leon.lang._

object MSTMap {

  case class Graph(nVertices : Int, edges : Map[(Int,Int), Int])

  /*
   -----------------------------------------------------------------------------
   MST TESTS Map
   -----------------------------------------------------------------------------
   */

  // Kruskal's algorithm. Straightforward imperative implementation
  def mst(g : Graph) : Map[(Int,Int), Int] = {
    require(invariant(g) && isUndirected(g) && isConnected(g) &&
  g.nVertices <= 3)

    var uf_map = Map.empty[Int, Int] //map to represent parent
    //relationship to model union find

    var spanningTree = Map.empty[(Int,Int), Int]
    var alreadyTested = Map.empty[(Int, Int), Int]

    (while(!isConnected(spanningTree, g.nVertices)) {
      val next_edge = getSmallestEdge(g.nVertices, g.edges, alreadyTested)

      val p1 = uFind(next_edge._1, uf_map)
      val p2 = uFind(next_edge._2, uf_map)
      if(p1  != p2) {
	// Edge doesn't create a cycle -> add it to the current
	// spanning tree (or actually forest)
	spanningTree = spanningTree.updated((next_edge._1, next_edge._2), next_edge._3)
	spanningTree = spanningTree.updated((next_edge._2, next_edge._1), next_edge._3)
	uf_map = union(p1, p2, uf_map)
      }

      alreadyTested = alreadyTested.updated((next_edge._1, next_edge._2), 1)
      alreadyTested = alreadyTested.updated((next_edge._2,
					     next_edge._1), 1)
    }) invariant(isAcyclic(spanningTree, g.nVertices))

    spanningTree
  } ensuring(x => isAcyclic(x, g.nVertices) && isConnected(x, g.nVertices))
  // We only verify that the edge set returned corresponds to some
  // spanning tree, but not that it is of minimal weight.


  // Here, we always take the smallest edge regardless whether it
  // creates a cycle or not,
  // Leon loops
  def mstBogus(g : Graph) : Map[(Int,Int), Int] = {
    require(invariant(g) && isUndirected(g) && isConnected(g) &&
  g.nVertices <= 4)

    var edges = g.edges
    var spanningTree = Map.empty[(Int,Int), Int]
    var alreadyTested = Map.empty[(Int, Int), Int]

    (while(!isConnected(spanningTree, g.nVertices)) {
      val next_edge = getSmallestEdge(g.nVertices, edges, alreadyTested)

      // add edge to spanning tree, don't care whether it creates a
      // cycle or not
      spanningTree = spanningTree.updated((next_edge._1, next_edge._2), next_edge._3)
      spanningTree = spanningTree.updated((next_edge._2, next_edge._1), next_edge._3)

      alreadyTested = alreadyTested.updated((next_edge._1, next_edge._2), 1)
      alreadyTested = alreadyTested.updated((next_edge._2,
					     next_edge._1), 1)
    }) invariant(isAcyclic(spanningTree, g.nVertices))

    spanningTree
  } ensuring(x => isAcyclic(x, g.nVertices) && isConnected(x, g.nVertices))


  /*
   -----------------------------------------------------------------------------
   GRAPH FUNCTIONS
   -----------------------------------------------------------------------------
   */


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
   * Returns the smallest edge in "edges" but not in "forbidden"
   * Returns (-1,-1,-1) if there are no more edges.
   */
  def getSmallestEdge(nVertices : Int, edges : Map[(Int,Int), Int],
		      forbidden : Map[(Int,Int), Int]) : (Int, Int, Int)
  = {
    require (nVertices >= 0)

    /*
     In the very specific context of MST, it could be useful to
     somehow express that "edges"\"forbidden" is non-empty such that
     it this function would always return a valid edge, however, this
     property is not easily expressible in Leon.
     */

    var i = 0
    val big = 100000000
    var res = (-1,-1,big)

      while(i < nVertices) {
	var j = 0
	while(j < nVertices) {
	  // leon doesnt recognize "shortcut optimizations", e.g. if
          // both if statements were merged to one using &&, it finds
          // a counter example
	  if(edges.isDefinedAt(i,j) && !forbidden.isDefinedAt(i,j)) {
	    if(edges(i,j) < res._3)
	      res = (i,j, edges(i,j))
	  }
	  j += 1
	}
	i += 1
      }

    if(res == (-1,-1,big))
      (-1,-1,-1)
    else
      res
  }

  def isSpanningTree(g : Graph) : Boolean = {
    require(invariant(g) && isUndirected(g))
    isConnected(g) && isAcyclic(g.edges, g.nVertices)
  }

   def isConnected(g : Graph) :  Boolean = {
     require(g.nVertices >= 0 && isUndirected(g))
     isConnected(g.edges, g.nVertices)
   }

  def isConnected(edges : Map[(Int,Int), Int], nVertices : Int) :  Boolean = {
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


  // fsc -d classes -classpath
  // ../../leon-2.0/target/scala-2.9.1-1/classes MST.scala
  //   scala -classpath classes MST
  @ignore
  def main(args: Array[String]) {
    val edges = Map((1,0) -> 10, (0,1) -> 10, (1,2) -> 12, (2,1) ->
  12, (0,2) -> 18, (2,0) -> 18, (3,1) -> 20, (1,3) -> 20)

    val g = Graph(4, edges)

    println(mst(g)); //works
    println(mstBogus(g)); // crashes because postcondition doensn't hold
  }

}
