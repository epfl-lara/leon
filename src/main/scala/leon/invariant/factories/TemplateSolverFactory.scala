/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.factories

import purescala.Definitions._
import purescala.Expressions._
import invariant._
import invariant.engine._
import invariant.util._
import invariant.structure._
import FunctionUtils._
import templateSolvers._
import leon.solvers.Model

object TemplateSolverFactory {

  def createTemplateSolver(ctx: InferenceContext, prog: Program, ctrack: ConstraintTracker, rootFun: FunDef,
    // options to solvers
    minopt: Option[(Expr, Model) => Model] = None,
    bound: Option[Int] = None): TemplateSolver = {
    if (ctx.useCegis) {
      // TODO: find a better way to specify CEGIS total time bound
      new CegisSolver(ctx, prog, rootFun, ctrack, 10000, bound)
    } else {
      val minimizer = if (ctx.tightBounds && rootFun.hasTemplate) {
        if (minopt.isDefined)
          minopt
        else {
          //TODO: need to assert that the templates are resource templates
          Some((new Minimizer(ctx, prog)).tightenTimeBounds(rootFun.getTemplate) _)
        }
      } else
        None
      if (ctx.withmult) {
        new NLTemplateSolverWithMult(ctx, prog, rootFun, ctrack, minimizer)
      } else {
        new NLTemplateSolver(ctx, prog, rootFun, ctrack, minimizer)
      }
    }
  }
}