import leon.annotation._
import leon.lang._

object SubgraphSet {
  case class Graph(nVertices : Int, edges : Map[(Int,Int), Int])
  
  /*
   -----------------------------------------------------------------------------
   SUBGRAPH TESTS
   -----------------------------------------------------------------------------
   */

  /*
   Empty graph is a subgraph of any other graph
   Works.
   */
  def empty(g : Graph) : Boolean = {
    require(invariant(g))
    val empty = Graph(0, Map.empty[(Int, Int), Int])
    isSubGraph(empty, g)
  } holds

  /*
   Graph with a single vertex is a subgraph of any other graph
   Finds counter example (empty graph) quickly
   */
  def singleGraphSubsetOfAnotherGraph(g : Graph) : Boolean = {
    require(invariant(g))
    val single = Graph(1, Map.empty[(Int, Int), Int])
    isSubGraph(single, g)
  } holds

  // Leon proves it quickly
  def subGraphIsReflexive(g : Graph) : Boolean = {
    require(invariant(g) && g.nVertices <=3)
    isSubGraph(g,g)
  } holds
  
  // Leon proves it within a few seconds (bounds!)
  def isSubGraphIsAntiSymmetric(g1 : Graph, g2 : Graph) : Boolean = {
    require(invariant(g1) && invariant(g2) && g1.nVertices <= 5 && g2.nVertices <= 5)
    !(isSubGraph(g1, g2) && isSubGraph(g2, g1)) || isEqual(g1, g2)
  } holds

  // Leon proves it within reasonable times (bounds!)
  def equalsIsSymmetric(g1 : Graph, g2 : Graph) : Boolean = {
    require(invariant(g1) && invariant(g2) && g1.nVertices <= 5 && g2.nVertices <= 5)
    isEqual(g1,g2) == isEqual(g2, g1)
  } holds

  
  /*
   -----------------------------------------------------------------------------
   GRAPH FUNCTIONS
   -----------------------------------------------------------------------------
   */

    // This rather weak invariant is good enough for our purposes here
  def invariant(g : Graph) = g.nVertices >= 0
  
  def isSubGraph(x : Graph, y : Graph) : Boolean = {
    require(invariant(x) && invariant(y))
    
    var ret : Boolean = (x.nVertices <= y.nVertices)
      if (ret){
	var i = 0
	while(i<x.nVertices) {
          var j = 0;
          while(j < x.nVertices) {
            ret &&= !x.edges.isDefinedAt((i,j)) || y.edges.isDefinedAt((i,j))

	    if(x.edges.isDefinedAt((i,j)) && y.edges.isDefinedAt((i,j)))
	      ret &&= (x.edges(i,j) == y.edges(i,j))
		
		j += 1
          }
          i += 1
	}
      }
    ret
  }

  def isEqual(x : Graph, y : Graph) : Boolean = {
    var ret = (x.nVertices == y.nVertices)
      var i = 0
    while(i<x.nVertices && ret) {
      var j = 0
      while(j < y.nVertices && ret) {
	
        ret &&= (!x.edges.isDefinedAt((i,j)) ||
		 y.edges.isDefinedAt((i,j))) && (!y.edges.isDefinedAt((i,j)) ||
						 x.edges.isDefinedAt((i,j)))
	if(x.edges.isDefinedAt((i,j)) && y.edges.isDefinedAt((i,j))) 
	  ret &&= (x.edges(i,j) == y.edges(i,j))
	    j += 1
	
      }
      i += 1
    }
    ret   
  }  
}
