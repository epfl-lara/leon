package purescala.z3plugins.bapa

import z3.scala.{Z3Context,Z3AST,Z3Theory}
import scala.collection.immutable.{Map=>ImmutableMap}

// This trait does involve reasoning about cardinalities, it just maintains a
// graph of inclusion between set terms.
// The goal is twofold: detect some equalities during the search (not so many
// probably) and some contradictions (even less), and have a good way to check
// for inclusion at finalCheck to avoid creating some Venn regions.
trait InclusionGraphs {
  val z3: Z3Context

  protected def assertAxiomEventually(ast: Z3AST) : Unit

  private type Z3ASTGraph = ImmutableMap[Z3AST,List[Z3AST]]

  object EmptyInclusionGraph {
    def apply() : InclusionGraph = new InclusionGraph(Nil, ImmutableMap.empty)
  }

  final class InclusionGraph private[InclusionGraphs](
    private val terms: List[Z3AST],
    private val graph: Z3ASTGraph) {

    def subsetOf(ast1: Z3AST, ast2: Z3AST) : Boolean = false
    def eq(ast1: Z3AST, ast2: Z3AST) : Boolean = subsetOf(ast1,ast2) && subsetOf(ast2,ast1)

    def newSubsetEq(ast1: Z3AST, ast2: Z3AST) : InclusionGraph = {
      this
    }

    def newEq(ast1: Z3AST, ast2: Z3AST) : InclusionGraph = {
      this
    }
  }
}
