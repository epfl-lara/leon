/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Quantification._
import purescala.ExprOps._

import solvers.Model

abstract class Evaluator(val context: LeonContext, val program: Program) extends LeonComponent {

  type EvaluationResult = EvaluationResults.Result

  /** Evaluates an expression, using `mapping` as a valuation function for the free variables. */
  def eval(expr: Expr, model: Model) : EvaluationResult

  /** Evaluates an expression given a simple model (assumes expr is quantifier-free).
    * Mainly useful for compatibility reasons.
    */
  final def eval(expr: Expr, mapping: Map[Identifier, Expr]) : EvaluationResult = eval(expr, new Model(mapping))

  /** Evaluates a ground expression. */
  final def eval(expr: Expr) : EvaluationResult = eval(expr, Model.empty)

  /** Compiles an expression into a function, where the arguments are the free variables in the expression.
    * `argorder` specifies in which order the arguments should be passed.
    * The default implementation uses the evaluation function each time, but evaluators are free
    * to (and encouraged to) apply any specialization. */
  def compile(expr: Expr, args: Seq[Identifier]) : Option[Model => EvaluationResult] = Some(
    (model: Model) => if(args.exists(arg => !model.isDefinedAt(arg))) {
      EvaluationResults.EvaluatorError("Wrong number of arguments for evaluation.")
    } else {
      eval (expr, model)
    }
  )
}

