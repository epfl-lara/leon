/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import leon.solvers.Model
import purescala.Expressions.Expr
import EvaluationResults._

class AngelicEvaluator(underlying: NDEvaluator)
  extends Evaluator(underlying.context, underlying.program)
     with DeterministicEvaluator {

  val description: String = "angelic evaluator"
  val name: String = "Interpreter that returns the first solution of a non-deterministic program"

  val bank = new EvaluationBank

  def eval(expr: Expr, model: Model): EvaluationResult = underlying.eval(expr, model) match {
    case Successful(Stream(h, _*)) =>
      Successful(h)
    case Successful(Stream()) =>
      RuntimeError("Underlying ND-evaluator returned no solution")
    case other@(RuntimeError(_) | EvaluatorError(_)) =>
      other.asInstanceOf[Result[Nothing]]
  }
}

class DemonicEvaluator(underlying: NDEvaluator)
  extends Evaluator(underlying.context, underlying.program)
     with DeterministicEvaluator {

  val description: String = "demonic evaluator"
  val name: String = "Interpreter that demands an underlying non-deterministic program has unique solution"

  val bank = new EvaluationBank

  def eval(expr: Expr, model: Model): EvaluationResult = underlying.eval(expr, model) match {
    case Successful(Stream(h)) =>
      Successful(h)
    case Successful(_) =>
      RuntimeError("Underlying ND-evaluator did not return unique solution!")
    case other@(RuntimeError(_) | EvaluatorError(_)) =>
      other.asInstanceOf[Result[Nothing]]
  }
}
