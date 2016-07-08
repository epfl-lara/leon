
package leon
package evaluators

import purescala.Expressions._
import purescala.Definitions._

class ProofEvaluator(ctx: LeonContext, prog: Program)
  extends DefaultEvaluator(ctx, prog) {

  override protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case _ => super.e(expr)(rctx, gctx)
  } 
}