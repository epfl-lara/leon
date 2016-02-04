/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._

import codegen.CompilationUnit
import codegen.CompiledExpression
import codegen.CodeGenParams

import leon.codegen.runtime.LeonCodeGenRuntimeException
import leon.codegen.runtime.LeonCodeGenEvaluationException
import leon.codegen.runtime.LeonCodeGenQuantificationException

class CodeGenEvaluator(ctx: LeonContext, val unit : CompilationUnit) extends Evaluator(ctx, unit.program) with DeterministicEvaluator {

  val name = "codegen-eval"
  val description = "Evaluator for PureScala expressions based on compilation to JVM"

  /** Another constructor to make it look more like other `Evaluator`s. */
  def this(ctx : LeonContext, prog : Program, params: CodeGenParams = CodeGenParams.default) {
    this(ctx, new CompilationUnit(ctx, prog, params))
  }

  private def compileExpr(expression: Expr, args: Seq[Identifier]): Option[CompiledExpression] = {
    ctx.timers.evaluators.codegen.compilation.start()
    try {
      Some(unit.compileExpression(expression, args)(ctx))
    } catch {
      case t: Throwable =>
        ctx.reporter.warning(expression.getPos, "Error while compiling expression: "+t.getMessage)
        None
    } finally {
      ctx.timers.evaluators.codegen.compilation.stop()
    }
  }


  def check(expression: Expr, fullModel: solvers.Model) : CheckResult = {
    val (_, assign) = fullModel.toSeq.partition {
      case (id, v) => unit.abstractFunDefs(id)
    }

    compileExpr(expression, assign.map(_._1)).map { ce =>
      ctx.timers.evaluators.codegen.runtime.start()

      try {
        val res = ce.eval(fullModel, check = true)

        if (res == BooleanLiteral(true)) {
          EvaluationResults.CheckSuccess
        } else {
          EvaluationResults.CheckValidityFailure
        }
      } catch {
        case e : ArithmeticException =>
          EvaluationResults.CheckRuntimeFailure(e.getMessage)

        case e : ArrayIndexOutOfBoundsException =>
          EvaluationResults.CheckRuntimeFailure(e.getMessage)

        case e : LeonCodeGenRuntimeException =>
          EvaluationResults.CheckRuntimeFailure(e.getMessage)

        case e : LeonCodeGenEvaluationException =>
          EvaluationResults.CheckRuntimeFailure(e.getMessage)

        case e : java.lang.ExceptionInInitializerError =>
          EvaluationResults.CheckRuntimeFailure(e.getException.getMessage) 

        case so : java.lang.StackOverflowError =>
          EvaluationResults.CheckRuntimeFailure("Stack overflow")

        case e : LeonCodeGenQuantificationException =>
          EvaluationResults.CheckQuantificationFailure(e.getMessage)
      } finally {
        ctx.timers.evaluators.codegen.runtime.stop()
      }
    }.getOrElse(EvaluationResults.CheckRuntimeFailure("Couldn't compile expression."))
  }

  def eval(expression: Expr, model: solvers.Model) : EvaluationResult = {
    compile(expression, model.toSeq.map(_._1)).map { e => 
      ctx.timers.evaluators.codegen.runtime.start()
      val res = e(model)
      ctx.timers.evaluators.codegen.runtime.stop()
      res
    }.getOrElse(EvaluationResults.EvaluatorError("Couldn't compile expression."))
  }

  override def compile(expression: Expr, args: Seq[Identifier]) : Option[solvers.Model=>EvaluationResult] = {
    compileExpr(expression, args).map(ce => (model: solvers.Model) => {
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
    }
  }
