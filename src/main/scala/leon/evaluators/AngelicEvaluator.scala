/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Definitions.Program
import purescala.Expressions.Expr

class AngelicEvaluator(ctx: LeonContext, prog: Program)
  extends ContextualEvaluator(ctx, prog, 50000)
  with DeterministicEvaluator
  with DefaultContexts
{
  private val underlying = new NDEvaluator(ctx, prog)

  val description: String = "angelic evaluator"
  val name: String = "Interpreter that returns the first solution of a non-deterministic program"

  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr =
    underlying.e(expr)(rctx, gctx).headOption.getOrElse(throw RuntimeError("No solution!"))
}
