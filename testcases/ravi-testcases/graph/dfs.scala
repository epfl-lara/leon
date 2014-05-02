import scala.collection.immutable._
import leon.annotation._
import leon.lang.invariantLang._

object DFS {
    
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
  def reach(src: Node, graph: Graph, reach: Set[Node]) : Set[Node] = {       
    require(Set(src).subsetOf(reach))            
    val neighs = graph.adjlist(src)
    val newreach = reachNodes(neighs, graph, reach)    	    	
    newreach
  } ensuring(res => time <= nodeSize(graph) - size(reach) + edgeSize(graph) - size(edgesFrom(reach)))
  
  def reachNodes(neighs: NodeList, graph: Graph, reach: Set[Node]) : Set[Node] = {        
    
    val newnodes = selectNewNodes(neighs, reach)
    val newreach = addToReach(reach, newnodes)
    callReachOnNodes(newnodes, graph, newreach)    
  } ensuring(res => time <= nodeSize(graph) - size(reach) + edgeSize(graph) - size(edgesFrom(reach)))
    
   //this method actually traverses the edges
   def callReachOnNodes(nodes: NodeList, graph: Graph, reach: Set[Node]) : Set[Node] = {
    nodes match {
      case Cons(node, tail) => reach(node, graph, reach) ++ callReachOnNodes(tail, graph, reach)
      case Nil() => reach
    }
  } ensuring(res => time <= nodeSize(graph) - size(reach) + edgeSize(graph) - size(edgesFrom(reach)) + size(nodes) + size(edgesFrom(content(nodes))))
  
   def selectNewNodes(nodes: NodeList, reach: Set[Node]) : NodeList = {
      nodes match {
      case Cons(node, tail) => 
        if(reach.contains(node)) 
         selectNewNodes(tail, reach)                
        else 
          Cons(node,selectNewNodes(tail, reach))
      }
   } ensuring(res => contents(res) ++ reach == reach ++ contents(nodes))
  
  def addToReach(reach: Set[Node], nodes : NodeList) : Set[Node] = {
    nodes match {
      case Cons(node, tail) => addToReach(Set(node) ++ reach, tail)
      case Nil() => reach
    }
  } ensuring(res => res == reach ++ contents(nodes))
  
  def contents(nodes: NodeList) : Set[Node] = {
    nodes match {
      case Cons(node, tail) => Set(node) ++ contents(nodes)
      case Nil() => Set[Node]()
    }
  }
  
  /*def reachValidity(src: Node, someNode: Node, graph: Graph) : Boolean = {
    val reachset = reach(src, graph, Set[Node]())
    if(Set(someNode).subsetOf(reachset)) {
       val neighs = graph.adjlist(someNode)
       contains(reachset, neighs)
    } else 
      true         
  } holds*/
  
  /*def contains(nodeset: Set[Node], keys: NodeList) : Boolean = {
    keys match {
      case Cons(node, tail) => Set(node).subsetOf(nodeset) && contains(nodeset, tail)
      case Nil() => true
    }
  }*/
 }
