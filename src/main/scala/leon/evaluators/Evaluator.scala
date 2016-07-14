/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._

import solvers.Model

import scala.collection.mutable.{Map => MutableMap}

abstract class Evaluator(val context: LeonContext, val program: Program) extends LeonComponent {

  /** The type of value that this [[Evaluator]] calculates
    * Typically, it will be [[Expr]] for deterministic evaluators, and
    * [[Stream[Expr]]] for non-deterministic ones.
    */
  type Value

  type EvaluationResult = EvaluationResults.Result[Value]

  /** Evaluates an expression, using [[Model.mapping]] as a valuation function for the free variables. */
  def eval(expr: Expr, model: Model) : EvaluationResult

  /** Evaluates an expression given a simple model (assumes expr is quantifier-free).
    * Mainly useful for compatibility reasons.
    */
  def eval(expr: Expr, mapping: Map[Identifier, Expr]) : EvaluationResult = eval(expr, new Model(mapping))

  /** Evaluates a ground expression. */
  final def eval(expr: Expr) : EvaluationResult = eval(expr, Model.empty)

  /** Compiles an expression into a function, where the arguments are the free variables in the expression.
    * `argorder` specifies in which order the arguments should be passed.
    * The default implementation uses the evaluation function each time, but evaluators are free
    * to (and encouraged to) apply any specialization.
    */
  def compile(expr: Expr, args: Seq[Identifier]) : Option[Model => EvaluationResult] = Some(
    (model: Model) => if(args.exists(arg => !model.isDefinedAt(arg))) {
      EvaluationResults.EvaluatorError("Wrong number of arguments for evaluation.")
    } else {
      eval (expr, model)
    }
  )
}

trait DeterministicEvaluator extends Evaluator {
  type Value = Expr

  val bank: EvaluationBank
  
  /**Evaluates the environment first, resolving non-cyclic dependencies, and then evaluate the expression */
  override def eval(expr: Expr, mapping: Map[Identifier, Expr]) : EvaluationResult = {
    if(mapping.forall{ case (key, value) => purescala.ExprOps.isValue(value) }) {
      super.eval(expr, mapping.toMap)
    } else {
      _evalEnv(mapping) match {
        case Left(m) => super.eval(expr, m)
        case Right(errorMessage) =>
          val m = mapping.filter { case (k, v) => purescala.ExprOps.isValue(v) }
          super.eval(expr, m) match {
            case res@EvaluationResults.Successful(result) => res
            case _ => EvaluationResults.EvaluatorError(errorMessage)
          }
      }
    }
  }

  /** Returns an evaluated environment. If it fails, removes all non-values from the environment. */
  def evalEnv(mapping: Iterable[(Identifier, Expr)]): Map[Identifier, Value] = {
    if(mapping.forall{ case (key, value) => purescala.ExprOps.isValue(value) }) {
      mapping.toMap
    } else {
      _evalEnv(mapping) match {
        case Left(m) => m
        case Right(msg) =>
          mapping.filter(x => purescala.ExprOps.isValue(x._2)).toMap
      }
    }
  }
  
  /** From a not yet well evaluated context with dependencies between variables, returns a head where all exprs are values (as a Left())
   *  If this does not succeed, it provides an error message as Right()*/
  private def _evalEnv(mapping: Iterable[(Identifier, Expr)]): Either[Map[Identifier, Value], String] = {
    val (evaled, nonevaled) = mapping.partition{ case (id, expr) => purescala.ExprOps.isValue(expr)}
    var f= nonevaled.toSet
    var mBuilder = scala.collection.mutable.ListBuffer[(Identifier, Value)]() ++= evaled
    var changed = true
    while(f.nonEmpty && changed) {
      changed = false
      for((i, v) <- f) {
        eval(v, mBuilder.toMap).result match {
          case None =>
          case Some(e) =>
            changed = true
            mBuilder += ((i -> e))
            f -= ((i, v))
        }
      }
    }
    if(!changed) {
      val str = "In the context " + mapping + ",\n" +
      (for((i, v) <- f) yield {
        s"eval($v) returned the error: " + eval(v, mBuilder.toMap)
      }).mkString("\n")
      Right(str)
    } else Left(mBuilder.toMap)
  }
}

trait NDEvaluator extends Evaluator {
  type Value = Stream[Expr]
}

/* Status of invariant checking
 *
 * For a given invariant, its checking status can be either
 * - Complete(success) : checking has been performed previously and
 *                       resulted in a value of `success`.
 * - Pending           : invariant is currently being checked somewhere
 *                       in the program. If it fails, the failure is
 *                       assumed to be bubbled up to all relevant failure
 *                       points.
 * - NoCheck           : invariant has never been seen before. Discovering
 *                       NoCheck for an invariant will automatically update
 *                       the status to `Pending` as this creates a checking
 *                       obligation.
 */
sealed abstract class CheckStatus {
  /* The invariant was invalid and this particular case class can't exist */
  def isFailure: Boolean = this match {
    case Complete(status) => !status
    case _ => false
  }

  /* The invariant has never been checked before and the checking obligation
   * therefore falls onto the first caller of this method. */
  def isRequired: Boolean = this == NoCheck
}

case class Complete(success: Boolean) extends CheckStatus
case object Pending extends CheckStatus
case object NoCheck extends CheckStatus

class EvaluationBank private(
  /* Shared set that tracks checked case-class invariants
   *
   * Checking case-class invariants can require invoking a solver
   * on a ground formula that contains a reference to `this` (the
   * current case class). If we then wish to check the model
   * returned by the solver, the expression given to the evaluator
   * will again contain the constructor for the current case-class.
   * This will create an invariant-checking loop.
   *
   * To avoid this problem, we introduce a set of invariants
   * that have already been checked that is shared between related
   * solvers and evaluators. This set is used by the evaluators to
   * determine whether the invariant of a given case
   * class should be checked.
   */
  checkCache: MutableMap[CaseClass, CheckStatus]) {

  def this() = this(MutableMap.empty)

  /* Status of the invariant checking for `cc` */
  def invariantCheck(cc: CaseClass): CheckStatus = synchronized {
    if (!cc.ct.classDef.hasInvariant) Complete(true)
    else checkCache.getOrElse(cc, {
      checkCache(cc) = Pending
      NoCheck
    })
  }

  /* Update the cache with the invariant check result for `cc` */
  def invariantResult(cc: CaseClass, success: Boolean): Unit = synchronized {
    checkCache(cc) = Complete(success)
  }

  override def clone: EvaluationBank = new EvaluationBank(checkCache.clone)
}
