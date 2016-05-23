/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.utils

import leon.test._
import leon.purescala.Common._
import leon.utils.Graphs._

class GraphsSuite extends LeonTestSuite {
  abstract class Node
  case object A extends Node
  case object B extends Node
  case object C extends Node
  case object D extends Node
  case object E extends Node
  case object F extends Node
  case object G extends Node
  case object H extends Node

  import scala.language.implicitConversions

  implicit def tToEdge(t: (Node, Node)): SimpleEdge[Node] = {
    SimpleEdge(t._1, t._2)
  }

  def g1 = {
    var g = new DiGraph[Node, SimpleEdge[Node]]()

    g ++= Set(A, B, C, D)

    g += A -> B
    g += B -> A

    g += B -> C

    g += C -> D
    g += D -> C

    // A   D
    // ↕   ↕
    // B → C

    g
  }

  def g2 = {
    var g = new DiGraph[Node, SimpleEdge[Node]]()

    g ++= Set(A, B, C, D)

    g += A -> B
    g += B -> B
    g += B -> C
    g += C -> D

    // A → B → C → D
    //    ↻

    g
  }

  def g3 = {
    var g = new DiGraph[Node, SimpleEdge[Node]]()

    g ++= Set(A, B, C, D, E, F, G, H)

    g += A -> B
    g += B -> C
    g += C -> D

    g += E -> A
    g += A -> F
    g += B -> F
    g += F -> E
    g += F -> G

    g += C -> G
    g += G -> C
    g += H -> G


    // A → B → C → D
    // ↑↘  ↓   ↕
    // E ← F → G ← H

    g
  }

  def g4 = {
    var g = new DiGraph[Node, SimpleEdge[Node]]()

    g ++= Set(A, B, C, D, E, F, G, H)

    g += A -> B
    g += B -> C
    g += C -> D

    g += A -> F
    g += B -> F
    g += F -> E
    g += F -> G

    g += C -> G
    g += H -> G


    // A → B → C → D
    //  ↘  ↓   ↓
    // E ← F → G ← H

    g
  }

  def g5 = {
    var g = new DiGraph[Node, SimpleEdge[Node]]()

    g ++= Set(A, B, C, D, E, F, G, H)

    g += A -> B
    g += B -> C

    g += A -> D
    g += D -> E


    // A → B → C   F   G   H
    //  ↘
    //     D → E

    g
  }


  test("Graphs basic 1") { ctx =>
    val g = g1
    assert(g.N.size === 4)
    assert(g.E.size === 5)

    assert(g.outEdges(A) === Set(SimpleEdge(A, B)))
    assert(g.outEdges(B) === Set(SimpleEdge(B, A), SimpleEdge(B, C)))

    assert(g.inEdges(B) === Set(SimpleEdge(A, B)))
    assert(g.inEdges(C) === Set(SimpleEdge(B, C), SimpleEdge(D, C)))

    assert(g.edgesBetween(A, B).size === 1)
  }

  test("Graphs sinks/sources 1") { ctx =>
    val g = g1

    assert(g.sources == Set())
    assert(g.sinks   == Set())
  }

  test("Graphs sinks/sources 2") { ctx =>
    val g = g2

    assert(g.N.size === 4)
    assert(g.E.size === 4)

    assert(g.sources == Set(A))
    assert(g.sinks   == Set(D))
  }

  test("Graphs SCC 1") { ctx =>
    val g = g1

    val gs = g.stronglyConnectedComponents

    assert(gs.N.size === 2)
    assert(gs.E.size === 1)
  }

  test("Graphs SCC 2") { ctx =>
    val g = g2

    val gs = g.stronglyConnectedComponents

    assert(gs.N.size === 4)
    assert(gs.E.size === 3)
  }

  test("Graphs SCC 3") { ctx =>
    val g = g3

    val gs = g.stronglyConnectedComponents

    assert(gs.N === Set(Set(A, B, E, F), Set(C, G), Set(D), Set(H)))
  }

  def assertBefore[T](s: Seq[T])(n1: T, n2: T) {
    assert(s.indexOf(n1) < s.indexOf(n2), s"Node '$n1' should be before '$n2'");
  }

  test("Graphs top-sort 1") { ctx =>
    val g = g4


    val seq = g.topSort

    val before = assertBefore(seq)_

    before(A, B)
    before(B, F)
    before(A, C)
  }

  test("Graphs top-sort 2 (cyclic graph fails)") { ctx =>
    val g = g1

    intercept[IllegalArgumentException] {
      g.topSort
    }
  }

  test("Graphs top-sort 3 (SCC is acyclic)") { ctx =>
    val g = g3

    val gs = g.stronglyConnectedComponents

    val c1: Set[Node] = Set(A, B, E, F)
    val c2: Set[Node] = Set(C, G)
    val c3: Set[Node] = Set(D)
    val c4: Set[Node] = Set(H)


    val ns = gs.topSort

    val before = assertBefore(ns)_
    before(c1, c2)
    before(c2, c3)
    before(c4, c2)
  }

  test("Graphs DFS") { ctx =>
    val g = g5

    var visited = List[Node]()
    g.depthFirstSearch(A) { n =>
      visited ::= n
    }
    visited = visited.reverse

    def isBefore(a: Node, b: Node) = visited.indexOf(a) < visited.indexOf(b)

    assert(!isBefore(B, D) || isBefore(C, E))
    assert(!isBefore(D, B) || isBefore(E, C))
  }

  test("Graphs BFS") { ctx =>
    val g = g5

    var visited = List[Node]()
    g.breadthFirstSearch(A) { n =>
      visited ::= n
    }
    visited = visited.reverse

    def isBefore(a: Node, b: Node) = visited.indexOf(a) < visited.indexOf(b)

    assert(isBefore(B, E))
    assert(isBefore(D, C))
  }

  test("Graphs pred/succ 1") { ctx =>
    val g = g2

    assert(g.succ(B) == Set(B, C))
    assert(g.pred(B) == Set(B, A))

    assert(g.transitiveSucc(B) == Set(B, C, D))
    assert(g.transitivePred(B) == Set(A, B))
    assert(g.transitivePred(C) == Set(A, B))
  }
}
