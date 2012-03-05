package leon.isabelle

import leon.Extensions._
import leon.Reporter
import leon.Settings._

import leon.purescala.Common.Identifier
import leon.purescala.Definitions._
import leon.purescala.PrettyPrinter
import leon.purescala.Trees._
import leon.purescala.TypeTrees._

import java.lang.StringBuffer
import java.io._
import java.util.Vector
import scala.collection.mutable.ListMap

//class to determine strongly connected components
object StrongConnectedComponents {
  def contains(v : Vector[String] , elem : String) : Boolean = {
	  for (i <- 0 until v.size)
	    if(v.elementAt(i).compareTo(elem) == 0)
	      return true
	  return false
  }
  

  //returns the strongly connected components of a graph in a list - each components is a list of vertices, or a list of Strings
  /*ALGORITHM (Kosaraju):
       * # Let G be a directed graph and S be an empty stack.
		# While S does not contain all vertices:
		    * Choose an arbitrary vertex v not in S. Perform a depth-first search starting at v. Each time that depth-first search 
		    * finishes expanding a vertex u, push u onto S.
		
		# Reverse the directions of all arcs to obtain the transpose graph.
		# While S is nonempty
		    * Pop the top vertex v from S. Perform a depth-first search starting at v. The set of visited vertices will give 
		    * the strongly connected component containing v; record this and remove all these vertices from the graph G and 
		    * the stack S.
    */

  def dfs_firstphase(current: String, graph: ListMap[String, List[String]], stack: Vector[String], visited: Vector[String]): Unit = {
    var o = graph.get(current)
    var list = Nil: List[String]
    o match {
      case None => list = Nil: List[String]
      case Some(l) => list = l
    }
    
    visited.add(current)
    
    for(s <- list)
      if(!contains(stack, s) && !contains(visited, s))
        dfs_firstphase(s,graph,stack, visited)
   
    stack.add(current)   
  }

  def dfs_secondphase(current: String, graph: ListMap[String, List[String]], visited: Vector[String]): Unit = {
    var o = graph.get(current)
    var list = Nil: List[String]
    o match {
      case None => list = Nil: List[String]
      case Some(l) => list = l
    }

    visited.add(current)

    for (s <- list)
      if (!contains(visited, s))
        dfs_secondphase(s, graph,visited)
  }

  def connectedComponents(graph : ListMap[String, List[String]]) : List[List[String]] = {
    var result = Nil : List[List[String]]
    var stack = new Vector[String]

    while(stack.size < graph.size){
      for(t <- graph)
    	  if(!contains(stack, t._1))
    		  dfs_firstphase(t._1, graph, stack, new Vector[String])          
    }
    
    var transposeGraph = new ListMap[String, List[String]]
    graph foreach( (t) =>{
    	t._2.foreach( p => {
		    var o = transposeGraph.get(p)
		    var list = Nil: List[String]
		    o match {
		      case None => list = Nil: List[String]
		      case Some(l) => list = l
		    }    		
		    transposeGraph.update(p, list ::: List(t._1))
    	})  
    }) 
   
    while(stack.size > 0){
    	var top = stack.remove(stack.size - 1)
    	var visited = new Vector[String]
    	dfs_secondphase(top, transposeGraph, visited)
    	var component = Nil : List[String]
    	for(i <- 0 until visited.size)
    	  component = component ::: List(visited.elementAt(i)) 
    	result = result ::: List(component)
    	for(el <- component){
    		var index = -1
    		for(i <- 0 until stack.size)
    		  if(stack.elementAt(i).compareTo(el) == 0)
    			  index = i
    		if(index > -1)
    			stack.remove(index)
    		transposeGraph = transposeGraph - el
		    transposeGraph foreach( (t) =>{
		      transposeGraph.update(t._1, t._2.filter(_ != el)) 
		    })     		
    	}
    }

    topologicalSort(graph, result)
    result
  }

  def contains(v : List[List[String]], elem : List[String]) : Boolean = {
	  for (el <- v)
	    if(el.head.compareTo(elem.head) == 0 && el.size == elem.size)
	      return true
	  return false
  }  
  
  //tests if component v1 has an edge to component v2
  def edgeTo(graph: ListMap[String, List[String]], v1 : List[String] , v2 : List[String]) : Boolean = {
   	  for(str1 <- v1){
   		  var o = graph.get(str1)
		  var list = Nil: List[String]
		  o match {
		  	case None => list = Nil: List[String]
		    case Some(l) => list = l
		  }    		  
   		  if(list.intersect(v2).size > 0)
   		    return true
   	  }
      return false
  }
  
  //sorts the connected components in a topological sort
  def topologicalSort(graph: ListMap[String, List[String]], components: List[List[String]]): List[List[String]] = {
	  
	  var sortedList = Nil: List[List[String]]
	  while (sortedList.size < components.size) 
	      for(current <- components)
	    	  if (!contains(sortedList, current)) {
	    		  var b = true
	    		  for(t <- components)
		        	  if (!contains(sortedList, t) && t != current) 
	        			  if(edgeTo(graph, t, current)){
	        			    b = false
	        			  }
		          if (b)
		        	  sortedList = sortedList ::: List(current)
	    	  }	  
	  sortedList
  }

  //returns the strongly connected components of the graph sorted in topological order using Kosaraju's algorithm
  def stronglyOrderedConnectedComponents(graph : ListMap[String, List[String]]) : List[List[String]] = {
    topologicalSort(graph, connectedComponents(graph))
  }
}
