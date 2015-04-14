/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

object Graphs {
  abstract class VertexAbs extends Serializable {
    val name: String

    override def toString = name
  }

  abstract class EdgeAbs[V <: VertexAbs] extends Serializable  {
    val v1: V
    val v2: V

    override def toString = v1 + "->" + v2
  }

  case class SimpleEdge[V <: VertexAbs](v1: V, v2: V) extends EdgeAbs[V]

  abstract class LabeledEdgeAbs[T, V <: VertexAbs] extends EdgeAbs[V] {
    val label: T
  }

  case class SimpleLabeledEdge[T, V <: VertexAbs](v1: V, label: T, v2: V) extends LabeledEdgeAbs[T, V]

  trait DirectedGraph[V <: VertexAbs, E <: EdgeAbs[V], G <: DirectedGraph[V,E,G]] extends Serializable {
    type Vertex = V
    type Edge   = E
    type This   = G

    // The vertices
    def V: Set[Vertex]
    // The edges
    def E: Set[Edge]
    // Returns the set of incoming edges for a given vertex
    def inEdges(v: Vertex)  = E.filter(_.v2 == v)
    // Returns the set of outgoing edges for a given vertex
    def outEdges(v: Vertex) = E.filter(_.v1 == v)

    // Returns the set of edges between two vertices
    def edgesBetween(from: Vertex, to: Vertex) = {
      E.filter(e => e.v1 == from && e.v2 == to)
    }

    /**
     * Basic Graph Operations:
     */

    // Adds a new vertex
    def + (v: Vertex): This
    // Adds new vertices
    def ++ (vs: Traversable[Vertex]): This
    // Adds a new edge
    def + (e: Edge): This
    // Removes a vertex from the graph
    def - (from: Vertex): This
    // Removes a number of vertices from the graph
    def -- (from: Traversable[Vertex]): This
    // Removes an edge from the graph
    def - (from: Edge): This

    /**
     * Advanced Graph Operations:
     */

    // Merges two graphs
    def union(that: This): This
    // Return the strongly connected components, sorted topologically
    def stronglyConnectedComponents: Seq[Set[Vertex]]
    // Topological sorting
    def topSort: Option[Seq[Vertex]]
    // All nodes leading to v
    def transitivePredecessors(v: Vertex): Set[Vertex]
    // All nodes reachable from v
    def transitiveSuccessors(v: Vertex): Set[Vertex]
    // Is v1 reachable from v2
    def isReachable(v1: Vertex, v2: Vertex): Boolean
  }

 case class DirectedGraphImp[Vertex <: VertexAbs, Edge <: EdgeAbs[Vertex]](
    vertices: Set[Vertex],
    edges: Set[Edge],
    ins: Map[VertexAbs, Set[Edge]],
    outs: Map[VertexAbs, Set[Edge]]
  ) extends DirectedGraph[Vertex, Edge, DirectedGraphImp[Vertex, Edge]] {

    override def equals(o: Any): Boolean = o match {
      case other: DirectedGraphImp[_, _] =>
        this.vertices == other.vertices &&
        this.edges    == other.edges &&
        (this.ins.keySet ++ other.ins.keySet).forall  (k   => this.ins(k)  == other.ins(k)) &&
        (this.outs.keySet ++ other.outs.keySet).forall(k => this.outs(k) == other.outs(k))

      case _ => false
    }

    def this (vertices: Set[Vertex], edges: Set[Edge]) =
      this(vertices,
           edges,
           edges.groupBy(_.v2: VertexAbs).withDefaultValue(Set()),
           edges.groupBy(_.v1: VertexAbs).withDefaultValue(Set()))

    def this() = this(Set(), Set())

    val V = vertices
    val E = edges

    def + (v: Vertex) = copy(
      vertices = vertices+v
    )

    override def inEdges(v: Vertex)  = ins(v)
    override def outEdges(v: Vertex) = outs(v)

    def ++ (vs: Traversable[Vertex]) = copy(
      vertices = vertices++vs
    )

    def -- (vs: Traversable[Vertex]) = copy(
      vertices = vertices--vs,
      edges    = edges -- vs.flatMap(outs) -- vs.flatMap(ins),
      ins      = ((ins -- vs)  map { case (vm, edges) => vm -> (edges -- vs.flatMap(outs)) }).withDefaultValue(Set()) ,
      outs     = ((outs -- vs) map { case (vm, edges) => vm -> (edges -- vs.flatMap(ins))  }).withDefaultValue(Set())
    )

    def + (e: Edge)   = copy(
      vertices = vertices + e.v1 + e.v2,
      edges    = edges + e,
      ins      = ins + (e.v2 -> (ins(e.v2) + e)),
      outs     = outs + (e.v1 -> (outs(e.v1) + e))
    )

    def - (v: Vertex) = copy(
      vertices = vertices-v,
      edges    = edges -- outs(v) -- ins(v),
      ins      = ((ins - v)  map { case (vm, edges) => vm -> (edges -- outs(v)) }).withDefaultValue(Set()) ,
      outs     = ((outs - v) map { case (vm, edges) => vm -> (edges -- ins(v))  }).withDefaultValue(Set())
    )

    def - (e: Edge)   = copy(
      vertices = vertices,
      edges    = edges-e,
      ins      = ins + (e.v2 -> (ins(e.v2) - e)),
      outs     = outs + (e.v1 -> (outs(e.v1) - e))
    )

    def union(that: This): This = copy(
      vertices = this.V ++ that.V,
      edges    = this.E ++ that.E,
      ins      = ((this.ins.keySet  ++ that.ins.keySet) map { k => k -> (this.ins(k) ++ that.ins(k)) }).toMap.withDefaultValue(Set()),
      outs     = ((this.outs.keySet ++ that.outs.keySet) map { k => k -> (this.outs(k) ++ that.outs(k)) }).toMap.withDefaultValue(Set())
    )

    def stronglyConnectedComponents: Seq[Set[Vertex]] = ???

    def topSort = {
      val sccs = stronglyConnectedComponents
      if (sccs.forall(_.size == 1)) {
        Some(sccs.flatten)
      } else {
        None
      }
    }

    def transitivePredecessors(v: Vertex): Set[Vertex] = {
      var seen = Set[Vertex]()
      def rec(v: Vertex): Set[Vertex] = {
        if (seen(v)) {
          Set()
        } else {
          seen += v
          val ins = inEdges(v).map(_.v1)
          ins ++ ins.map(rec).flatten
        }
      }
      rec(v)
    }

    def transitiveSuccessors(v: Vertex): Set[Vertex] = {
      var seen = Set[Vertex]()
      def rec(v: Vertex): Set[Vertex] = {
        if (seen(v)) {
          Set()
        } else {
          seen += v
          val outs = outEdges(v).map(_.v2)
          outs ++ outs.map(rec).flatten
        }
      }
      rec(v)
    }

    def isReachable(v1: Vertex, v2: Vertex): Boolean = {
      var seen = Set[Vertex]()
      def rec(v: Vertex): Boolean = {
        if (seen(v)) {
          false
        } else {
          seen += v
          val outs = outEdges(v).map(_.v2)
          if (outs(v2)) {
            true
          } else {
            outs.map(rec).foldLeft(false)( _ || _ )
          }
        }
      }
      rec(v1)
    }

    override def toString = "DGraph[V: "+vertices+" | E:"+edges+"]"
  }
}
