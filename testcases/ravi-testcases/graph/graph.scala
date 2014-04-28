import scala.collection.immutable._
import leon.annotation._
import leon.lang.invariantLang._

object Graph {
    
  case class Node(id: Int)
  case class Edge(src : Node, dst: Node)
  //a graph is a set of nodes with ids 1...nv and a mapping from vertices to incident edges
  case class Graph(nv : Int, adjlist : Map[Node,NodeList])  
  sealed abstract class NodeList  
  case class Cons(node: Node, tail: NodeList) extends NodeList
  case class Nil() extends NodeList
    
  //checks if a node is a valid node of a graph
  /*def validNode(node: Node, graph: Graph) : Boolean = {
    node.id >= 1 && node.id <= graph.nv 
  }
  //checks if edges refer to valid vertices
  def validNodes(nodes: NodeList, graph: Graph) : Boolean = {
    nodes match {
      case Cons(node,tail) => 
        validNode(node, graph) && validNodes(tail, graph)            
      case Nil() => true
    }
  }
  
  def validAdjList(nid: Int, graph: Graph) : Boolean = {
    require(nid >= 1)    
    if(nid > graph.nv) true
    else {
      graph.adjlist.isDefinedAt(Node(nid) 
          && validNodes(graph.adjlist(Node(nid))) 
          && validAdjList(nid + 1, graph)             
    }
  } 
  
  def vaildGraph(graph : Graph) : Boolean ={
    graph.nv >= 1 && validAdjList(1, graph)     
  }
  
  def nodesRec(nid: Int, g : Graph) : Set[Node] = {
    if(nid > g.nv) Set[Node]()
    else{
     Set[Node](Node(nid)) ++ nodesRec(nid + 1, g)
    }
  }
  
  def nodes(g : Graph) : Set[Node] = {
     nodesRec(1, g) 
  }    */  
  
  //a DFS operation on graphs
  //returns a set of nodes that have been completely processed and a set of visited nodes and 
  def reach(src: Node, graph: Graph, finished: Set[Node], visited: Set[Node], someNode: Node) 
  	: (Set[Node], Set[Node], Set[Node]) = ({       
    require(finished.subsetOf(visited))
    
    if(visited.contains(src)) (finished, Set.empty[Node], visited)
    else {
    	val neighs = graph.adjlist(src)
    	val (nfin, unfin, nvisit) = reachNodes(neighs, graph, finished, visited ++ Set(src), someNode)    	    	
    	if((unfin -- visited) == Set.empty[Node]) {
    	  (nfin ++ unfin ++ Set(src), Set.empty[Node], nvisit)
    	} else { 
    	  (nfin, unfin ++ Set(src), nvisit)
    	}
    }
  }) ensuring(res => {
    val (fin, unfin, visit) = res    
    ( visit == (fin ++ unfin ++ visited)  
      && finished.subsetOf(fin)
      && (fin ++ unfin).subsetOf(visit)      
      && ((visited == Set.empty[Node]) || Set(src).subsetOf(fin)) 
      && (!Set(someNode).subsetOf(unfin) || contains(fin ++ unfin ++ visited, graph.adjlist(someNode)))
      && (!Set(someNode).subsetOf(fin) || contains(fin, graph.adjlist(someNode)))
      )      
  })
  
  def reachNodes(nodes: NodeList, graph: Graph, finished: Set[Node], visited: Set[Node], someNode: Node) 
  	: (Set[Node], Set[Node], Set[Node]) = {    
    require(finished.subsetOf(visited))
    
    nodes match {
      case Cons(node, tail) => 
        if(visited.contains(node)) {
          if(finished.contains(node)) {
            //this node has been visited, need not do anything here.
            reachNodes(tail, graph, finished, visited, someNode)   
          } else{
            //this is an unfinishable visit
        	val (nfin, unfin, nvisit) = reachNodes(tail, graph, finished, visited, someNode)
        	(nfin, unfin ++ Set(node), nvisit)
          }          
        } 
        else {          
          val (nfin0, unfin0, nvisit0) = reach(node, graph, finished, visited, someNode)          
          val (nfin, unfin, nvisit) = reachNodes(tail, graph, nfin0, nvisit0, someNode)
          (nfin, unfin0 ++ unfin, nvisit) 
        }
      case Nil() => (finished, Set.empty[Node], visited)
    }
  } ensuring(res => {
    val (fin, unfin, visit) = res
    (visit == (fin ++ unfin ++ visited) 
      && finished.subsetOf(fin)      
      && contains(fin ++ unfin, nodes)
      && (!Set(someNode).subsetOf(unfin) || contains(fin ++ unfin ++ visited, graph.adjlist(someNode)))
      && (!Set(someNode).subsetOf(fin) || contains(fin, graph.adjlist(someNode)))
      )
    })
  
  /*def reachValidity(src: Node, someNode: Node, graph: Graph) : Boolean = {
    val reachset = reach(src, graph, Set[Node]())
    if(Set(someNode).subsetOf(reachset)) {
       val neighs = graph.adjlist(someNode)
       contains(reachset, neighs)
    } else 
      true         
  } holds*/
  
  def contains(nodeset: Set[Node], keys: NodeList) : Boolean = {
    keys match {
      case Cons(node, tail) => Set(node).subsetOf(nodeset) && contains(nodeset, tail)
      case Nil() => true
    }
  }
 }
