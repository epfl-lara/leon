/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package repair
package rules

import synthesis._

import leon.utils.Simplifiers
import purescala.Expressions._
import purescala.Definitions._
import purescala.Common._
import purescala.Types._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._

import Witnesses._

import solvers._
import graph._

case object GuidedCloser extends NormalizingRule("Guided Closer") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    hctx.parentNode match {
      case Some(an: AndNode) if an.ri.rule == GuidedDecomp =>
        // We proceed as usual
      case _ =>
        return Nil
    }

    val TopLevelAnds(clauses) = p.ws

    val guides = clauses.collect {
      case Guide(expr) => expr
    }

    val alts = guides.filter(isDeterministic).flatMap { e =>
      // Tentative solution using e

      val simp = Simplifiers.bestEffort(hctx.context, hctx.program) _

      val vc = simp(and(p.pc, letTuple(p.xs, e, not(p.phi))))

      val solver = hctx.sctx.newSolver.setTimeout(2000L)

      solver.assertCnstr(vc)
      val osol = solver.check match {
        case Some(false) =>
          Some(Solution(BooleanLiteral(true), Set(), e, true))

        case None =>
          hctx.reporter.ifDebug { printer =>
            printer(vc)
            printer("== Unknown ==")
          }
          //None
          //Some(Solution(BooleanLiteral(true), Set(), wrappedE, false))
          None

        case _ =>
          hctx.reporter.ifDebug { printer =>
            printer(vc)
            printer("== Invalid! ==")
          }
          None
      }

      solver.free

      osol.map { solve }

    }

    alts
  }
}
