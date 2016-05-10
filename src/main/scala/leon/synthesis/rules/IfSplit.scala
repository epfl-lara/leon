/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.solvers._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Constructors._

case object IfSplit extends Rule("If-Split") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    def split(i: IfExpr, description: String): Option[RuleInstantiation] = {

      val solver = SimpleSolverAPI(SolverFactory.getFromSettings(hctx, hctx.program).withTimeout(1000))
      if (
        solver.solveVALID(p.pc implies     i.cond ).contains(true) ||
        solver.solveVALID(p.pc implies not(i.cond)).contains(true)
      ){
        // Condition can only go one way, no reason to split...
        return None
      }

      val subs = List(
        Problem(p.as, p.ws, p.pc withCond i.cond, replace(Map(i -> i.thenn), p.phi), p.xs),
        Problem(p.as, p.ws, p.pc withCond not(i.cond), replace(Map(i -> i.elze), p.phi), p.xs)
      )

      val onSuccess: List[Solution] => Option[Solution] = {
        case sols if sols.size == 2 =>
          val List(ts, es) = sols

          val pre = or(and(i.cond, ts.pre), and(not(i.cond), es.pre))
          val defs = ts.defs ++ es.defs
          val term = IfExpr(i.cond, ts.term, es.term)

          Some(Solution(pre, defs, term, sols.forall(_.isTrusted)))

        case _ =>
          None
      }

      Some(decomp(subs, onSuccess, description))
    }

    val ifs = collect{
      case i: IfExpr => Set(i)
      case _ => Set[IfExpr]()
    }(p.phi)

    val xsSet = p.xs.toSet

    ifs.flatMap { 
      case i @ IfExpr(cond, _, _) =>
        if ((variablesOf(cond) & xsSet).isEmpty) {
          split(i, s"If-Split on '${cond.asString}'")
        } else {
          None
        }
    }

  }
}

