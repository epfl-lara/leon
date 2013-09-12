/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import utils._
import purescala.Common._
import purescala.Trees._

trait Solver extends Interruptible {
  def push(): Unit
  def pop(lvl: Int = 1): Unit
  def assertCnstr(expression: Expr): Unit

  def check: Option[Boolean]
  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean]
  def getModel: Map[Identifier, Expr]
  def getUnsatCore: Set[Expr]

  implicit val debugSection = DebugSectionSolver
}
