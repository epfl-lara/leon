/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

object Graphs {
  trait EdgeLike[Node] {
    def _1: Node
    def _2: Node
  }

  case class SimpleEdge[Node](_1: Node, _2: Node) extends EdgeLike[Node]
  case class LabeledEdge[Label, Node](_1: Node, l: Label, _2: Node) extends EdgeLike[Node]

  trait DiGraphLike[Node, Edge <: EdgeLike[Node], G <: DiGraphLike[Node, Edge, G]] {
    // The vertices
    def N: Set[Node]
    // The edges
    def E: Set[Edge]

    // Returns the set of incoming edges for a given vertex
    def inEdges(n: Node)  = E.filter(_._2 == n)
    // Returns the set of outgoing edges for a given vertex
    def outEdges(n: Node)  = E.filter(_._1 == n)

    // Returns the set of edges between two vertices
    def edgesBetween(from: Node, to: Node) = {
      E.filter(e => e._1 == from && e._2 == to)
    }

    // Adds a new vertex
    def + (n: Node): G
    // Adds new vertices
    def ++ (ns: Traversable[Node]): G
    // Adds a new edge
    def + (e: Edge): G
    // Removes a vertex from the graph
    def - (from: Node): G
    // Removes a number of vertices from the graph
    def -- (from: Traversable[Node]): G
    // Removes an edge from the graph
    def - (from: Edge): G
  }

  case class DiGraph[Node, Edge <: EdgeLike[Node]](N: Set[Node] = Set[Node](), E: Set[Edge] = Set[Edge]()) extends DiGraphLike[Node, Edge, DiGraph[Node, Edge]] with DiGraphOps[Node, Edge, DiGraph[Node, Edge]]{
    def +(n: Node) = copy(N=N+n)
    def ++(ns: Traversable[Node]) = copy(N=N++ns)
    def +(e: Edge) = (this+e._1+e._2).copy(E = E + e)

    def -(n: Node) = copy(N = N-n, E = E.filterNot(e => e._1 == n || e._2 == n))
    def --(ns: Traversable[Node]) = {
      val toRemove = ns.toSet
      copy(N = N--ns, E = E.filterNot(e => toRemove.contains(e._1) || toRemove.contains(e._2)))
    }

    def -(e: Edge) = copy(E = E-e)
  }


  trait DiGraphOps[Node, Edge <: EdgeLike[Node], G <: DiGraphLike[Node, Edge, G]] {
    this: G =>

    def sources: Set[Node] = {
      N -- E.map(_._2)
    }

    def sinks: Set[Node] = {
      N -- E.map(_._1)
    }

    def stronglyConnectedComponents: DiGraph[Set[Node], SimpleEdge[Set[Node]]] = {
      // Tarjan's algorithm
      var index = 0
      var stack = List[Node]()

      var indexes  = Map[Node, Int]()
      var lowlinks = Map[Node, Int]()
      var onStack  = Set[Node]()

      var nodesToScc = Map[Node, Set[Node]]()
      var res = DiGraph[Set[Node], SimpleEdge[Set[Node]]]()

      def strongConnect(n: Node): Unit = {
        indexes  += n -> index
        lowlinks += n -> index
        index += 1

        stack = n :: stack
        onStack += n

        for (m <- succ(n)) {
          if (!(indexes contains m)) {
            strongConnect(m)
            lowlinks += n -> (lowlinks(n) min lowlinks(m))
          } else if (onStack(m)) {
            lowlinks += n -> (lowlinks(n) min indexes(m))
          }
        }

        if (lowlinks(n) == indexes(n)) {
          val i = stack.indexOf(n)+1
          val ns = stack.take(i)
          stack = stack.drop(i)
          val scc = ns.toSet
          onStack --= ns
          nodesToScc ++= ns.map(n => n -> scc)
          res += scc
        }
      }


      for (n <- N if !(indexes contains n)) {
        strongConnect(n)
      }

      for (e <- E) {
        val s1 = nodesToScc(e._1)
        val s2 = nodesToScc(e._2)
        if (s1 != s2) {
          res += SimpleEdge(s1, s2)
        }
      }

      res
    }

    def topSort: Seq[Node] = {
      var res = List[Node]()

      var temp = Set[Node]()
      var perm = Set[Node]()

      def visit(n: Node) {
        if (temp(n)) {
          throw new IllegalArgumentException("Graph is not a DAG")
        } else if (!perm(n)) {
          temp += n
          for (n2 <- succ(n)) {
            visit(n2)
          }
          perm += n
          temp -= n
          res ::= n
        }
      }

      for (n <- N if !temp(n) && !perm(n)) {
        visit(n)
      }

      res
    }

    def depthFirstSearch(from: Node)(f: Node => Unit): Unit = {
      var visited = Set[Node]()

      val stack = new collection.mutable.Stack[Node]()

      stack.push(from)

      while(stack.nonEmpty) {
        val n = stack.pop
        visited += n
        f(n)
        for (n2 <- succ(n) if !visited(n2)) {
          stack.push(n2)
        }
      }
    }

    def fold[T](from: Node)(
      follow: Node => Traversable[Node],
      map: Node => T,
      compose: List[T] => T): T = {

      var visited = Set[Node]()

      def visit(n: Node): T = {
        visited += n

        val toFollow = follow(n).filterNot(visited)
        visited ++= toFollow

        compose(map(n) :: toFollow.toList.map(visit))
      }

      compose(follow(from).toList.map(visit))
    }

    def succ(from: Node): Set[Node] = {
      outEdges(from).map(_._2)
    }

    def pred(from: Node): Set[Node] = {
      inEdges(from).map(_._1)
    }

    def transitiveSucc(from: Node): Set[Node] = {
      fold[Set[Node]](from)(
        succ,
        Set(_),
        _.toSet.flatten
      )
    }

    def transitivePred(from: Node): Set[Node] = {
      fold[Set[Node]](from)(
        pred,
        Set(_),
        _.toSet.flatten
      )
    }

    def breadthFirstSearch(from: Node)(f: Node => Unit): Unit = {
      var visited = Set[Node]()

      val queue = new collection.mutable.Queue[Node]()

      queue += from

      while(queue.nonEmpty) {
        val n = queue.dequeue
        visited += n
        f(n)
        for (n2 <- succ(n) if !visited(n2)) {
          queue += n2
        }
      }
    }
  }
}
