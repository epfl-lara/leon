/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import utils._
import purescala.Expressions.Expr
import purescala.Common.Identifier


trait Solver {
  def name: String
  val context: LeonContext

  implicit lazy val leonContext = context

  def assertCnstr(expression: Expr): Unit

  def check: Option[Boolean]
  def getModel: Map[Identifier, Expr]

  def free()

  implicit val debugSection = DebugSectionSolver

  private[solvers] def debugS(msg: String) = {
    context.reporter.debug("["+name+"] "+msg)
  }
}
