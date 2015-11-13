/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import leon.utils.{DebugSectionSolver, Interruptible}
import purescala.Expressions._
import purescala.Common.Tree
import verification.VC

trait Solver extends Interruptible {
  def name: String
  val context: LeonContext

  implicit lazy val leonContext = context

  // This is ugly, but helpful for smtlib solvers
  def dbg(msg: => Any) {}

  def assertCnstr(expression: Expr): Unit
  def assertVC(vc: VC) = {
    dbg(s"; Solving $vc @ ${vc.getPos}\n")
    assertCnstr(Not(vc.condition))
  }

  def check: Option[Boolean]
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
    leonContext.reporter.warning(err.getMessage)
    throw err
  }

  protected def unsupported(t: Tree, str: String): Nothing = {
    val err = SolverUnsupportedError(t, this, Some(str))
    leonContext.reporter.warning(err.getMessage)
    throw err
  }

  implicit val debugSection = DebugSectionSolver

  private[solvers] def debugS(msg: String) = {
    context.reporter.debug("["+name+"] "+msg)
  }
}
