/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import leon.solvers.Model
import purescala.Definitions.Program
import purescala.Expressions.Expr
import EvaluationResults._

class AngelicEvaluator(ctx: LeonContext, prog: Program, underlying: NDEvaluator)
  extends Evaluator(ctx, prog)
  with DeterministicEvaluator
{
  val description: String = "angelic evaluator"
  val name: String = "Interpreter that returns the first solution of a non-deterministic program"

  def eval(expr: Expr, model: Model): EvaluationResult = underlying.eval(expr, model) match {
    case Successful(Stream(h, _*)) =>
      Successful(h)
    case Successful(Stream()) =>
      RuntimeError("Underlying ND-evaluator returned no solution")
    case other@(RuntimeError(_) | EvaluatorError(_)) =>
      other.asInstanceOf[Result[Nothing]]
  }
}
