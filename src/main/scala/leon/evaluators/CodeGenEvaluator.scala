/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Quantification._

import codegen.CompilationUnit
import codegen.CodeGenParams

class CodeGenEvaluator(ctx: LeonContext, val unit : CompilationUnit) extends Evaluator(ctx, unit.program) {
  val name = "codegen-eval"
  val description = "Evaluator for PureScala expressions based on compilation to JVM"

  /** Another constructor to make it look more like other `Evaluator`s. */
  def this(ctx : LeonContext, prog : Program, params: CodeGenParams = CodeGenParams.default) {
    this(ctx, new CompilationUnit(ctx, prog, params))
  }

  def eval(expression: Expr, model: solvers.Model) : EvaluationResult = {
    val toPairs = model.toSeq
    compile(expression, toPairs.map(_._1)).map { e =>
      ctx.timers.evaluators.codegen.runtime.start()
      val res = e(model)
      ctx.timers.evaluators.codegen.runtime.stop()
      res
    }.getOrElse(EvaluationResults.EvaluatorError("Couldn't compile expression."))
  }

  override def compile(expression: Expr, args: Seq[Identifier]) : Option[solvers.Model=>EvaluationResult] = {
    import leon.codegen.runtime.LeonCodeGenRuntimeException
    import leon.codegen.runtime.LeonCodeGenEvaluationException

    ctx.timers.evaluators.codegen.compilation.start()
    try {
      val ce = unit.compileExpression(expression, args)(ctx)

      Some((model: solvers.Model) => {
        if (args.exists(arg => !model.isDefinedAt(arg))) {
          EvaluationResults.EvaluatorError("Model undefined for free arguments")
        } else try {
          EvaluationResults.Successful(ce.eval(model))
        } catch {
          case e : ArithmeticException =>
            EvaluationResults.RuntimeError(e.getMessage)

          case e : ArrayIndexOutOfBoundsException =>
            EvaluationResults.RuntimeError(e.getMessage)

          case e : LeonCodeGenRuntimeException =>
            EvaluationResults.RuntimeError(e.getMessage)

          case e : LeonCodeGenEvaluationException =>
            EvaluationResults.EvaluatorError(e.getMessage)

          case e : java.lang.ExceptionInInitializerError =>
            EvaluationResults.RuntimeError(e.getException.getMessage)

          case so : java.lang.StackOverflowError =>
            EvaluationResults.RuntimeError("Stack overflow")

        }
      })
    } catch {
      case t: Throwable =>
        ctx.reporter.warning(expression.getPos, "Error while compiling expression: "+t.getMessage)
        None
    } finally {
      ctx.timers.evaluators.codegen.compilation.stop()
    }
  }
}
