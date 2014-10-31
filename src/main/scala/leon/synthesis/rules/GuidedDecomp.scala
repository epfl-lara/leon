/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Definitions._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

import solvers._

case object GuidedDecomp extends Rule("Guided Decomp") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(clauses) = p.pc

    val guide = sctx.program.library.guide.get

    val guides = clauses.collect {
      case FunctionInvocation(TypedFunDef(`guide`, _), Seq(expr)) => expr
    }

    val alts = guides.collect {
      case g @ IfExpr(c, thn, els) =>
        val sub1 = p.copy(pc = And(c, replace(Map(g -> thn), p.pc)))
        val sub2 = p.copy(pc = And(Not(c), replace(Map(g -> els), p.pc)))

        val onSuccess: List[Solution] => Option[Solution] = { 
          case List(s1, s2) =>
            Some(Solution(Or(s1.pre, s2.pre), s1.defs++s2.defs, IfExpr(c, s1.term, s2.term)))
          case _ =>
            None
        }

        Some(RuleInstantiation.immediateDecomp(p, this, List(sub1, sub2), onSuccess, "Guided If-Split on '"+c+"'"))

      case e =>
       None
    }

    alts.flatten
  }
}
