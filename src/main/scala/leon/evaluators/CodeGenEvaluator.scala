package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._
import purescala.TypeTrees._

import codegen.CompilationUnit

class CodeGenEvaluator(ctx : LeonContext, val unit : CompilationUnit) extends Evaluator(ctx, unit.program) {
  val name = "codegen-eval"
  val description = "Evaluator for PureScala expressions based on compilation to JVM"

  /** Another constructor to make it look more like other `Evaluator`s. */
  def this(ctx : LeonContext, prog : Program) {
    this(ctx, CompilationUnit.compileProgram(prog).get) // this .get is dubious...
  }

  def eval(expression : Expr, mapping : Map[Identifier,Expr]) : EvaluationResult = {
    // ctx.reporter.warning("Using `eval` in CodeGenEvaluator is discouraged. Use `compile` whenever applicable.")

    val toPairs = mapping.toSeq
    compile(expression, toPairs.map(_._1)).map(e => e(toPairs.map(_._2))).getOrElse(EvaluationResults.EvaluatorError("Couldn't compile expression."))
  }

  override def compile(expression : Expr, argorder : Seq[Identifier]) : Option[Seq[Expr]=>EvaluationResult] = {
    import leon.codegen.runtime.LeonCodeGenRuntimeException
    import leon.codegen.runtime.LeonCodeGenEvaluationException

    try {
      val ce = unit.compileExpression(expression, argorder)

      Some((args : Seq[Expr]) => {
        try {
          EvaluationResults.Successful(ce.eval(args))
        } catch {
          case e : ArithmeticException =>
            EvaluationResults.RuntimeError(e.getMessage)

          case e : ArrayIndexOutOfBoundsException =>
            EvaluationResults.RuntimeError(e.getMessage)

          case e : LeonCodeGenRuntimeException =>
            EvaluationResults.RuntimeError(e.getMessage)

          case e : LeonCodeGenEvaluationException =>
            EvaluationResults.EvaluatorError(e.getMessage)
        }
      })
    } catch {
      case t: Throwable =>
        ctx.reporter.warning("Error while compiling expression: "+t.getMessage)
        None
    }
  }
}
