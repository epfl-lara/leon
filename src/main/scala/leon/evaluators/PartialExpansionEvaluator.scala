/* Copyright 2009-2017 EPFL, Lausanne */

package leon
package evaluators

import leon.grammars.{ExpansionExpr, NonTerminalInstance, ProdRuleInstance}
import leon.purescala.Definitions.Program
import leon.purescala.Expressions.Expr

class PartialExpansionEvaluator(ctx: LeonContext, prog: Program, bank: EvaluationBank = new EvaluationBank)
    extends TableEvaluator(ctx, prog, bank) {

  override protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case ExpansionExpr(NonTerminalInstance(_)) => throw new EvalError("Full evaluation failed!")
    case ExpansionExpr(ProdRuleInstance(nt, rule, children)) =>
      val childExprs = children map ExpansionExpr
      val falseExpr = rule.builder(childExprs)
      e(falseExpr)(rctx, gctx)
    case other => super.e(other)
  }

}
