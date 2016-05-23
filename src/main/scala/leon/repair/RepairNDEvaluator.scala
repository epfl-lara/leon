/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package repair

import purescala.Definitions.Program
import purescala.Expressions._
import purescala.ExprOps.valuesOf
import evaluators.StreamEvaluator

/** A [[leon.evaluators.StreamEvaluator StreamEvaluator]] that treats a specified expression [[nd]] as a non-deterministic value
  * @note Expressions are compared against [[nd]] with reference equality.
  */
class RepairNDEvaluator(ctx: LeonContext, prog: Program, nd: Expr) extends StreamEvaluator(ctx, prog) {

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Stream[Expr] = expr match {
    case Not(c) if c eq nd =>
      // This is a hack: We know the only way nd is wrapped within a Not is if it is NOT within
      // a recursive call. So we need to treat it deterministically at this point...
      super.e(c) collect { case BooleanLiteral(b) => BooleanLiteral(!b) }
    case c if c eq nd =>
      valuesOf(c.getType)
    case other =>
      super.e(other)
  }

}
