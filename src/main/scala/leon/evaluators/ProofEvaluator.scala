
package leon
package evaluators

import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Types._

import leon.verification.VerificationContext
import leon.verification.theorem._

class ProofEvaluator(ctx: VerificationContext, prog: Program)
  extends DefaultEvaluator(ctx, prog) {

  private var vcs: Seq[Expr] = Seq()
  val library = new Library(prog)
  val encoder = new ExprEncoder(ctx)

  override protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case FunctionInvocation(TypedFunDef(fd, Seq()), Seq(arg)) if (fd == library.prove.get) => {
      ctx.reporter.info("Called solve.")
      val evaluatedArg = e(arg)
      addVCExpr(evaluatedArg)
      super.e(FunctionInvocation(TypedFunDef(fd, Seq()), Seq(evaluatedArg)))
    }
    case FunctionInvocation(TypedFunDef(fd, Seq()), Seq(arg)) if (fd == library.fresh.get) => {
      ctx.reporter.info("Called fresh.")
      val StringLiteral(name) = e(arg)
      val freshName = FreshIdentifier(name, Untyped, true).uniqueName
      encoder.caseClass(library.Identifier, StringLiteral(freshName))
    }
    case _ => super.e(expr)
  }

  private def addVCExpr(expr: Expr): Unit = vcs = vcs :+ expr
  def resetVCExpres: Unit = vcs = Seq()
  def getVCExprs: Seq[Expr] = vcs
}