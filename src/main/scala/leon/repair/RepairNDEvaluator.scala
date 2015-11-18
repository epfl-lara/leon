/* Copyright 2009-2015 EPFL, Lausanne */

package leon.repair

import leon.purescala._
import Definitions._
import Expressions._
import leon.LeonContext
import leon.evaluators.StreamEvaluator

/** This evaluator treats the expression [[expr]] (reference equality) as a non-deterministic value */
class RepairNDEvaluator(ctx: LeonContext, prog: Program, expr: Expr) extends StreamEvaluator(ctx, prog) {

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Stream[Expr] = expr match {
    case c if c eq expr =>
      e(NDValue(c.getType))
    case other =>
      super.e(other)
  }

}
