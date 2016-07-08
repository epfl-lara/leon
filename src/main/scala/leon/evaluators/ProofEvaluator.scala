
package leon
package evaluators

import purescala.Expressions._
import purescala.Definitions._

import leon.verification.theorem._

class ProofEvaluator(ctx: LeonContext, prog: Program)
  extends DefaultEvaluator(ctx, prog) {

  private var vcs: Seq[Expr] = Seq()
  val library = new Library(prog)

  override protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case FunctionInvocation(TypedFunDef(fd, Seq()), Seq(arg)) if (fd == library.prove.get) => {
      ctx.reporter.info("Called solve.")
      val evaluatedArg = e(arg)
      addVCExpr(evaluatedArg)
      super.e(FunctionInvocation(TypedFunDef(fd, Seq()), Seq(evaluatedArg)))
    }
    case _ => super.e(expr)
  }

  private def addVCExpr(expr: Expr): Unit = vcs = vcs :+ expr
  def resetVCExpres: Unit = vcs = Seq()
  def getVCExprs: Seq[Expr] = vcs
}