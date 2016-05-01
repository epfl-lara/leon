/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import leon.utils.{DebugSectionSolver, Interruptible}
import purescala.Expressions._
import purescala.Common.Tree
import verification.VC
import evaluators._

case class SolverContext(context: LeonContext, bank: EvaluationBank) {
  lazy val reporter = context.reporter
  override def clone = SolverContext(context, bank.clone)
}

trait Solver extends Interruptible {
  def name: String
  val sctx: SolverContext

  implicit lazy val context = sctx.context
  lazy val reporter = sctx.reporter

  // This is ugly, but helpful for smtlib solvers
  def dbg(msg: => Any) {}

  def assertCnstr(expression: Expr): Unit
  def assertVC(vc: VC) = {
    dbg(s"; Solving $vc @ ${vc.getPos}\n")
    assertCnstr(Not(vc.condition))
  }

  /** Returns Some(true) if it found a satisfying model, Some(false) if no model exists, and None otherwise */
  def check: Option[Boolean]
  /** Returns the model if it exists */
  def getModel: Model
  def getResultSolver: Option[Solver] = Some(this)

  def free()

  def reset()

  def push(): Unit
  def pop(): Unit

  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean]
  def getUnsatCore: Set[Expr]

  protected def unsupported(t: Tree): Nothing = {
    val err = SolverUnsupportedError(t, this, None)
    context.reporter.warning(err.getMessage)
    throw err
  }

  protected def unsupported(t: Tree, str: String): Nothing = {
    val err = SolverUnsupportedError(t, this, Some(str))
    //leonContext.reporter.warning(str)
    throw err
  }

  implicit val debugSection = DebugSectionSolver

  private[solvers] def debugS(msg: String) = {
    context.reporter.debug("["+name+"] "+msg)
  }
}
