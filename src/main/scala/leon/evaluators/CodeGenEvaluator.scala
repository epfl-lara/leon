/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._
import purescala.TypeTrees._

import codegen.CompilationUnit
import codegen.CodeGenParams

class CodeGenEvaluator(ctx : LeonContext, val unit : CompilationUnit) extends Evaluator(ctx, unit.program) {
  val name = "codegen-eval"
  val description = "Evaluator for PureScala expressions based on compilation to JVM"

  /** Another constructor to make it look more like other `Evaluator`s. */
  def this(ctx : LeonContext, prog : Program, params: CodeGenParams = CodeGenParams()) {
    this(ctx, new CompilationUnit(ctx, prog, params))
  }

  def eval(expression : Expr, mapping : Map[Identifier,Expr]) : EvaluationResult = {
    val toPairs = mapping.toSeq
    val compiled = compile(expression, toPairs.map(_._1))
    val applied = compiled.map(e => e(toPairs.map(_._2)))
    applied.getOrElse(EvaluationResults.EvaluatorError("Couldn't compile expression."))
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
