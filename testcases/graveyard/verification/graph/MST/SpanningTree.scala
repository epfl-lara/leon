import leon.annotation._
import leon.lang._

object SpanningTree {
  case class Graph(nVertices : Int, edges : Set[(Int,Int)])

  // Kruskal on unweighted graphs (thus not spanning tree of minimum weight)
  def getSpanningTree(g : Graph) : Set[(Int, Int)] = {
    require(invariant(g) && isUndirected(g) && isConnected(g.edges,
							   g.nVertices) && g.nVertices <= 3)

    var uf_map = Map.empty[Int, Int] //map to represent parent
    //relationship to model union find
    
    var spanningSet = Set.empty[(Int,Int)]
    var remainingEdges = g.edges
    
    (while(!isConnected(spanningSet, g.nVertices)) {
      val next_edge = epsilon( (i : (Int, Int)) =>
	remainingEdges.contains(i) )

      val p1 = uFind(next_edge._1, uf_map)
      val p2 = uFind(next_edge._2, uf_map)
      if(p1  != p2) {
	spanningSet = spanningSet ++ Set(next_edge) ++
	Set((next_edge._2, next_edge._1))

	uf_map = union(p1, p2, uf_map)
      }
      
      remainingEdges = remainingEdges -- Set(next_edge) -- Set((next_edge._2, next_edge._1))

    }) invariant(isAcyclic(spanningSet, g.nVertices))

    spanningSet
  } ensuring(x => isAcyclic(x, g.nVertices))
  
  def getSpanningTreeBogus(g : Graph) : Set[(Int, Int)] = {
    require(invariant(g) && isUndirected(g) && isConnected(g.edges,
				       		   g.nVertices) && g.nVertices <= 4)

    var spanningSet = Set.empty[(Int,Int)]
    var remainingEdges = g.edges
    
    (while(!isConnected(spanningSet, g.nVertices)) {
      val next_edge = epsilon( (i : (Int, Int)) => remainingEdges.contains(i) )
      remainingEdges = remainingEdges -- Set(next_edge) -- Set((next_edge._2, next_edge._1))

      spanningSet = spanningSet ++ Set(next_edge) ++ Set((next_edge._2, next_edge._1))
    }) invariant(isAcyclic(spanningSet, g.nVertices))

    spanningSet
  } ensuring(x => isAcyclic(x, g.nVertices))

  
  def invariant(g : Graph) = {
    def noSelfLoops(i : Int) : Boolean = {
      if(i >= g.nVertices) true
      else if(g.edges.contains(i,i))
	false
      else
	noSelfLoops(i+1)
    }
    
    g.nVertices >= 0 // && noSelfLoops(0)
  }

  /*
   Smarter version of doing it?
   */
  def isUndirected(g : Graph) : Boolean = {
    def isUndirected0(s : Set[(Int, Int)]) : Boolean= {
      if(s == Set.empty[(Int,Int)]) true
      else {
	val e = epsilon( (p : (Int,Int)) => s.contains(p) )
	if(g.edges.contains(e))
	  isUndirected0(s -- Set(e))
	else
	  false
      }
    }

    isUndirected0(g.edges)
  }

  /*
   * Tests, whether the subgraph induced by edges is cycle-free.
   */
  def isAcyclic(edges : Set[(Int,Int)], nVertices : Int) : Boolean = {
    require(nVertices >= 0 && isUndirected(Graph(nVertices, edges)))
    !calculateUF(edges, nVertices)._2
  }
  
  /*
   * Does union-find on edgeSet.
   * Returns the union-find tree and a boolean set to true if a cycle was found
   */
  def calculateUF(edgeSet : Set[(Int,Int)], nVertices : Int) :
  (Map[Int, Int], Boolean)= {
    require(nVertices >= 0)
    
    var i = 0
    var uf = Map.empty[Int, Int]
    var cycle = false
    var edges = edgeSet
    while(i < nVertices) {
      var j = 0
      while(j < i) {
	if(edges.contains((i,j))) {
	    val p1 = uFind(i, uf)
	    val p2 = uFind(j, uf)
	    if(p1 == p2)
	      cycle = true
	    else
	      uf = union(p1, p2, uf)
	}
      
	j += 1
      }
      i += 1
    }

    (uf, cycle)
  }

  def isConnected(edges : Set[(Int,Int)], nVertices : Int) :  Boolean
  = {
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

  def testUndirected() : Boolean = {
    val e = Set.empty[(Int, Int)] ++ Set((1,2)) ++ Set((2,1)) ++ Set((1,3))
    isUndirected(Graph(4, e))
  } holds
  
}
