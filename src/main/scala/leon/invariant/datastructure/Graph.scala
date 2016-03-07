/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.datastructure

class DirectedGraph[T] {

  var adjlist = scala.collection.mutable.Map[T, Set[T]]()
  var edgeCount: Int = 0

  def addNode(n: T) {
    if (!adjlist.contains(n)) {
      adjlist.update(n, Set())
    }
  }

  def addEdge(src: T, dest: T): Unit = {
    val newset = if (adjlist.contains(src)) adjlist(src) + dest
    else Set(dest)

    //this has some side-effects
    adjlist.update(src, newset)

    edgeCount += 1
  }

  def BFSReach(src: T, dest: T, excludeSrc: Boolean = false): Boolean = {
    var queue = List[T]()
    var visited = Set[T]()
    visited += src

    //TODO: is there a better (and efficient) way to implement BFS without using side-effects
    def BFSReachRecur(cur: T): Boolean = {
      var found: Boolean = false
      if (adjlist.contains(cur)) {
        adjlist(cur).foreach((fi) => {
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
    var queue = List[T]()
    var visited = Set[T]()
    visited ++= srcs.toSet

    def BFSReachRecur(cur: T): Unit = {
      if (adjlist.contains(cur)) {
        adjlist(cur).foreach((neigh) => {
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

    srcs.foreach{src => BFSReachRecur(src) }
    visited
  }

  def containsEdge(src: T, dest: T): Boolean = {
    if (adjlist.contains(src)) {
      adjlist(src).contains(dest)
    } else false
  }

  def getEdgeCount: Int = edgeCount
  def getNodes: Set[T] = adjlist.keySet.toSet
  def getSuccessors(src: T): Set[T] = adjlist(src)

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
      val strslt = getSuccessors(vertex).foldLeft(newState)(processNeighbor)
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
    val totalNodes = getNodes
    while (state.visited.size < totalNodes.size) {
      totalNodes.find(n => !state.visited.contains(n)).foreach { n =>
        state = search(n, state)
      }
    }
    state.components
  }

  /**
   * Reverses the direction of the edges in the graph
   */
  def reverse : DirectedGraph[T] = {
    val revg = new DirectedGraph[T]()
    adjlist.foreach{
      case (src, dests) =>
        dests.foreach { revg.addEdge(_, src) }
    }
    revg
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
}
