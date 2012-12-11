package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._

abstract class Evaluator(val context : LeonContext, val program : Program) extends LeonComponent {

  /** Evaluates an expression, using `mapping` as a valuation function for the free variables. */
  def eval(expr : Expr, mapping : Map[Identifier,Expr]) : EvaluationResult

  /** Evaluates a ground expression. */
  final def eval(expr : Expr) : EvaluationResult = eval(expr, Map.empty)

  /** Compiles an expression into a function, where the arguments are the free variables in the expression.
    * `argorder` specifies in which order the arguments should be passed.
    * The default implementation uses the evaluation function each time, but evaluators are free
    * to (and encouraged to) apply any specialization. */
  def compile(expr : Expr, argorder : Seq[Identifier]) : Option[Seq[Expr]=>EvaluationResult] = Some(
    (args : Seq[Expr]) => if(args.size != argorder.size) {
        EvaluationError("Wrong number of arguments for evaluation.")
    } else {
      val mapping = argorder.zip(args).toMap
      eval(expr, mapping)
    }
  )
}

/** Possible results of expression evaluation. */
sealed abstract class EvaluationResult(val result : Option[Expr])

/** Represents an evaluation that successfully derived the result `value`. */
case class EvaluationSuccessful(value : Expr) extends EvaluationResult(Some(value))

/** Represents an evaluation that led to an error (in the program). */
case class EvaluationFailure(message : String) extends EvaluationResult(None)

/** Represents an evaluation that failed (in the evaluator). */
case class EvaluationError(message : String) extends EvaluationResult(None)
