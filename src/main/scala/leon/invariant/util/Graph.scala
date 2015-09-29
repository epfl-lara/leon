package leon
package invariant.util

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

  def BFSReachables(src: T): Set[T] = {
    var queue = List[T]()
    var visited = Set[T]()
    visited += src

    def BFSReachRecur(cur: T): Unit = {
      if (adjlist.contains(cur)) {
        adjlist(cur).foreach((neigh) => {
          if (!visited.contains(neigh)) {
            visited += neigh
            queue ::= neigh
          }
        })
      }
      if (!queue.isEmpty) {
        val (head :: tail) = queue
        queue = tail
        BFSReachRecur(head)
      }
    }

    BFSReachRecur(src)
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
   * Change this to the verified component
   */
  def sccs: List[List[T]] = {

    type Component = List[T]

    case class State(count: Int,
      visited: Map[T, Boolean],
      dfNumber: Map[T, Int],
      lowlinks: Map[T, Int],
      stack: List[T],
      components: List[Component])

    def search(vertex: T, state: State): State = {
      val newState = state.copy(visited = state.visited.updated(vertex, true),
        dfNumber = state.dfNumber.updated(vertex, state.count),
        count = state.count + 1,
        lowlinks = state.lowlinks.updated(vertex, state.count),
        stack = vertex :: state.stack)

      def processVertex(st: State, w: T): State = {
        if (!st.visited(w)) {
          val st1 = search(w, st)
          val min = Math.min(st1.lowlinks(w), st1.lowlinks(vertex))
          st1.copy(lowlinks = st1.lowlinks.updated(vertex, min))
        } else {
          if ((st.dfNumber(w) < st.dfNumber(vertex)) && st.stack.contains(w)) {
            val min = Math.min(st.dfNumber(w), st.lowlinks(vertex))
            st.copy(lowlinks = st.lowlinks.updated(vertex, min))
          } else st
        }
      }

      val strslt = getSuccessors(vertex).foldLeft(newState)(processVertex)

      if (strslt.lowlinks(vertex) == strslt.dfNumber(vertex)) {

        val index = strslt.stack.indexOf(vertex)
        val (comp, rest) = strslt.stack.splitAt(index + 1)
        strslt.copy(stack = rest,
          components = strslt.components :+ comp)
      } else strslt
    }

    val initial = State(
      count = 1,
      visited = getNodes.map { (_, false) }.toMap,
      dfNumber = Map(),
      lowlinks = Map(),
      stack = Nil,
      components = Nil)

    var state = initial
    while (state.visited.exists(_._2 == false)) {
      state.visited.find(_._2 == false).foreach { tuple =>
        val (vertex, _) = tuple
        state = search(vertex, state)
      }
    }
    state.components
  }

}

class UndirectedGraph[T] extends DirectedGraph[T] {

  override def addEdge(src: T, dest: T): Unit = {
    val newset1 = if (adjlist.contains(src)) adjlist(src) + dest
    else Set(dest)

    val newset2 = if (adjlist.contains(dest)) adjlist(dest) + src
    else Set(src)

    //this has some side-effects
    adjlist.update(src, newset1)
    adjlist.update(dest, newset2)

    edgeCount += 1
  }
}
