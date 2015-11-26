/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

object EvaluationResults {
  /** Possible results of expression evaluation. */
  sealed abstract class Result[+A](val result : Option[A])

  /** Represents an evaluation that successfully derived the result `value`. */
  case class Successful[A](value : A) extends Result(Some(value))

  /** Represents an evaluation that led to an error (in the program). */
  case class RuntimeError(message : String) extends Result(None)

  /** Represents an evaluation that failed (in the evaluator). */
  case class EvaluatorError(message : String) extends Result(None)

  /** Results of checking proposition evaluation.
   *  Useful for verification of model validity in presence of quantifiers. */
  sealed abstract class CheckResult(val success: Boolean)

  /** Successful proposition evaluation (model |= expr) */
  case object CheckSuccess extends CheckResult(true)

  /** Check failed with `model |= !expr` */
  case object CheckValidityFailure extends CheckResult(false)

  /** Check failed due to evaluation or runtime errors.
   *  @see [[RuntimeError]] and [[EvaluatorError]] */
  case class CheckRuntimeFailure(msg: String) extends CheckResult(false)

  /** Check failed due to inconsistence of model with quantified propositions. */
  case class CheckQuantificationFailure(msg: String) extends CheckResult(false)
}
