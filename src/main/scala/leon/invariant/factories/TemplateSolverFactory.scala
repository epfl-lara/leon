package leon
package invariant.factories

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import invariant._
import invariant.engine._
import invariant.util._
import invariant.structure._
import FunctionUtils._
import templateSolvers._
import leon.solvers.Model

object TemplateSolverFactory {

  def createTemplateSolver(ctx: InferenceContext, ctrack: ConstraintTracker, rootFun: FunDef,
    // options to solvers
    minopt: Option[(Expr, Model) => Model] = None,
    bound: Option[Int] = None): TemplateSolver = {
    if (ctx.useCegis) {
      // TODO: find a better way to specify CEGIS total time bound
      new CegisSolver(ctx, rootFun, ctrack, 10000, bound)
    } else {
      val minimizer = if (ctx.tightBounds && rootFun.hasTemplate) {
        if (minopt.isDefined)
          minopt
        else {
          //TODO: need to assert that the templates are resource templates
          Some((new Minimizer(ctx)).tightenTimeBounds(rootFun.getTemplate) _)
        }
      } else
        None
      if (ctx.withmult) {
        new NLTemplateSolverWithMult(ctx, rootFun, ctrack, minimizer)
      } else {
        new NLTemplateSolver(ctx, rootFun, ctrack, minimizer)
      }
    }
  }
}