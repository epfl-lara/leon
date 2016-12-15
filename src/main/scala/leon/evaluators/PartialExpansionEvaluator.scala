package leon
package evaluators

import leon.grammars.{ExpansionExpr, NonTerminalInstance, ProdRuleInstance}
import leon.purescala.Definitions.Program
import leon.purescala.Expressions.Expr

// The following code has been grafted together from DefaultEvaluator and RecursiveEvaluator.

class PartialExpansionEvaluator(ctx: LeonContext, prog: Program, bank: EvaluationBank = new EvaluationBank)
  extends TableEvaluator(ctx, prog, bank)
    with HasDefaultGlobalContext
    with HasDefaultRecContext {

  override protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case ExpansionExpr(NonTerminalInstance(_)) => throw new EvalError("Full evaluation failed!")
    case ExpansionExpr(ProdRuleInstance(nt, rule, children)) =>
      val childExprs = children map ExpansionExpr
      val falseExpr = rule.builder(childExprs)
      e(falseExpr)(rctx, gctx)
    case other => super.e(other)
  }

}
