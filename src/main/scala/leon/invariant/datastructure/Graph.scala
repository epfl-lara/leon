/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.datastructure
import purescala.Definitions._

/**
 * The trait represents a graph-like data structure supporting the following operations.
 */
trait Graph[T] {

  def nodes: Set[T]

  def successors(src: T): Set[T]

  def edgeCount: Int

  def containsEdge(src: T, dest: T): Boolean

  def BFSReach(src: T, dest: T, excludeSrc: Boolean = false): Boolean = {
    val nods = nodes
    var queue = List[T]()
    var visited = Set[T]()
    visited += src
    //TODO: is there a better (and efficient) way to implement BFS without using side-effects
    def BFSReachRecur(cur: T): Boolean = {
      var found: Boolean = false
      if (nods(cur)) {
        successors(cur).foreach((fi) => {
          if (fi == dest) found = true
          else if (!visited.contains(fi)) {
            visited += fi
            queue ::= fi
          }
        })
      }
      if (found) true
      else if (queue.isEmpty) false
      else {
        val (head :: tail) = queue
        queue = tail
        BFSReachRecur(head)
      }
    }

    if (!excludeSrc && src == dest) true
    else BFSReachRecur(src)
  }

  def BFSReachables(srcs: Seq[T]): Set[T] = {
    val nods = nodes
    var queue = List[T]()
    var visited = Set[T]()
    visited ++= srcs.toSet

    def BFSReachRecur(cur: T): Unit = {
      if (nods(cur)) {
        successors(cur).foreach((neigh) => {
          if (!visited.contains(neigh)) {
            visited += neigh
            queue ::= neigh
          }
        })
      }
      if (queue.nonEmpty) {
        val (head :: tail) = queue
        queue = tail
        BFSReachRecur(head)
      }
    }
    srcs.foreach { src => BFSReachRecur(src) }
    visited
  }

  /**
   * TODO: Change this to the verified component
   * The computed nodes are also in reverse topological order.
   */
  def sccs: List[List[T]] = {

    type Component = List[T]

    case class State(count: Int,
                     visited: Set[T],
                     dfNumber: Map[T, Int],
                     lowlinks: Map[T, Int],
                     stack: List[T],
                     components: List[Component])

    def search(vertex: T, state: State): State = {
      val newState = state.copy(visited = state.visited + vertex,
        dfNumber = state.dfNumber + (vertex -> state.count),
        count = state.count + 1,
        lowlinks = state.lowlinks + (vertex -> state.count),
        stack = vertex :: state.stack)

      def processNeighbor(st: State, w: T): State = {
        if (!st.visited(w)) {
          val st1 = search(w, st)
          val min = Math.min(st1.lowlinks(w), st1.lowlinks(vertex))
          st1.copy(lowlinks = st1.lowlinks + (vertex -> min))
        } else {
          if ((st.dfNumber(w) < st.dfNumber(vertex)) && st.stack.contains(w)) {
            val min = Math.min(st.dfNumber(w), st.lowlinks(vertex))
            st.copy(lowlinks = st.lowlinks + (vertex -> min))
          } else st
        }
      }
      val strslt = successors(vertex).foldLeft(newState)(processNeighbor)

      if (strslt.lowlinks(vertex) == strslt.dfNumber(vertex)) {
        val index = strslt.stack.indexOf(vertex)
        val (comp, rest) = strslt.stack.splitAt(index + 1)
        strslt.copy(stack = rest,
          components = strslt.components :+ comp)
      } else strslt
    }
    val initial = State(
      count = 1,
      visited = Set(),
      dfNumber = Map(),
      lowlinks = Map(),
      stack = Nil,
      components = Nil)

    var state = initial
    val totalNodes = nodes
    while (state.visited.size < totalNodes.size) {
      totalNodes.find(n => !state.visited.contains(n)).foreach { n =>
        state = search(n, state)
      }
    }
    state.components
  }

  def reverse: Graph[T]
}

/**
 * A mutable directed graph.
 * We can add and also remove edges from this graph.
 */
class DirectedGraph[T] extends Graph[T] {

  val adjlist = scala.collection.mutable.Map[T, Set[T]]()
  var edgeCount: Int = 0

  def addNode(n: T) {
    if (!adjlist.contains(n)) {
      adjlist.update(n, Set())
    }
  }

  def addEdge(src: T, dest: T) {
    if (!containsEdge(src, dest)) {
      val newset = adjlist.getOrElse(src, Set[T]()) + dest
      adjlist.update(src, newset)
      edgeCount += 1
    }
  }

  def removeEdge(src: T, dest: T): Unit = {
    if (adjlist.contains(src) && adjlist(src).contains(dest)) {
      val nset = adjlist(src) - dest
      adjlist.update(src, nset)
      edgeCount -= 1
    }
  }

  def containsEdge(src: T, dest: T): Boolean = {
    if (adjlist.contains(src)) {
      adjlist(src).contains(dest)
    } else false
  }

  def nodes: Set[T] = adjlist.keySet.toSet

  def successors(src: T): Set[T] = adjlist(src)
  /**
   * Reverses the direction of the edges in the graph
   */
  def reverse = {
    val revg = new DirectedGraph[T]()
    adjlist.foreach {
      case (src, dests) =>
        dests.foreach { revg.addEdge(_, src) }
    }
    revg
  }

  def copy: DirectedGraph[T] = {
    val ng = new DirectedGraph[T]()
    adjlist.foreach { case (k, v) => ng.adjlist.update(k, v) }
    ng.edgeCount = this.edgeCount
    ng
  }
}

class UndirectedGraph[T] extends DirectedGraph[T] {

  override def addEdge(src: T, dest: T): Unit = {
    val newset1 =
      if (adjlist.contains(src)) adjlist(src) + dest
      else Set(dest)
    val newset2 =
      if (adjlist.contains(dest)) adjlist(dest) + src
      else Set(src)
    //this has some side-effects
    adjlist.update(src, newset1)
    adjlist.update(dest, newset2)
    edgeCount += 1
  }

  override def removeEdge(src: T, dest: T): Unit = throw new IllegalStateException("Not yet implemented!")

}

/**
 * A directed graph with labels
 */
class DirectedLabeledGraph[T, L](private val dgraph: DirectedGraph[T] = new DirectedGraph[T]()) extends Graph[T] {
  type Edge = (T, T)
  val labels = scala.collection.mutable.Map[Edge, Set[L]]()

  def addNode(n: T) = dgraph.addNode(n)

  def addEdge(src: T, dest: T, label: L) {
    dgraph.addEdge(src, dest)
    val key = (src, dest)
    labels.update(key, labels.getOrElse(key, Set[L]()) + label)
  }

  def removeEdgesWithLabels(remlabels: Set[L]) = {
    val nlg = new DirectedLabeledGraph[T, L](dgraph.copy)
    var edgesToRemove = Set[Edge]()
    labels.foreach {
      case (edge, edgeLabels) if (edgeLabels -- remlabels).isEmpty =>
        edgesToRemove += edge
      case (edge, edgeLabels) =>
        nlg.labels.update(edge, (edgeLabels -- remlabels))
    }
    edgesToRemove.foreach { case (src, dest) => nlg.dgraph.removeEdge(src, dest) }
    nlg
  }

  def projectOnLabel(label: L): DirectedGraph[T] = {
    val ng = dgraph.copy
    var edgesToRemove = Set[Edge]()
    labels.foreach {
      case (edge, edgeLabels) if !edgeLabels(label) => edgesToRemove += edge
      case _                                        =>
    }
    edgesToRemove.foreach { case (src, dest) => ng.removeEdge(src, dest) }
    ng
  }

  def reverse = {
    val nlg = new DirectedLabeledGraph[T, L](dgraph.reverse)
    labels.foreach {
      case ((src, dest), ls) => nlg.labels.update((dest, src), ls)
    }
    nlg
  }

  /**
   * Label agnostic procedures
   */
  def containsEdge(src: T, dest: T): Boolean = dgraph.containsEdge(src, dest)

  def successors(src: T): Set[T] = dgraph.successors(src)

  def edgeCount: Int = dgraph.edgeCount

  def nodes: Set[T] = dgraph.nodes

  def succsWithLabels(src: T): Map[T, Set[L]] = {
    successors(src).map { dst =>
      dst -> labels.getOrElse((src, dst), Set[L]())
    }.toMap
  }
}
