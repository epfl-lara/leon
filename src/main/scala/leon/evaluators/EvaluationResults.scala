/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package evaluators

import purescala.Expressions.Expr

object EvaluationResults {
  /** Possible results of expression evaluation. */
  sealed abstract class Result(val result : Option[Expr])

  /** Represents an evaluation that successfully derived the result `value`. */
  case class Successful(value : Expr) extends Result(Some(value))

  /** Represents an evaluation that led to an error (in the program). */
  case class RuntimeError(message : String) extends Result(None)

  /** Represents an evaluation that failed (in the evaluator). */
  case class EvaluatorError(message : String) extends Result(None)
}
