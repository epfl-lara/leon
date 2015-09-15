/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.z3

import z3.scala._

import leon.solvers._
import utils.IncrementalSet

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._

/** This is a rather direct mapping to Z3, where all functions are left uninterpreted.
 *  It reports the results as follows (based on the negation of the formula):
 *    - if Z3 reports UNSAT, it reports VALID
 *    - if Z3 reports SAT and the formula contained no function invocation, it returns INVALID with the counter-example/model
 *    - otherwise it returns UNKNOWN
 *  Results should come back very quickly.
 */
class UninterpretedZ3Solver(val context : LeonContext, val program: Program)
  extends AbstractZ3Solver
     with Z3ModelReconstruction {

  val name = "Z3-u"
  val description = "Uninterpreted Z3 Solver"

  // this is fixed
  protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )
  toggleWarningMessages(true)

  initZ3()

  val solver = z3.mkSolver()

  def push() {
    solver.push()
    freeVariables.push()
  }

  def pop() {
    solver.pop(1)
    freeVariables.pop()
  }

  private val freeVariables = new IncrementalSet[Identifier]()

  def assertCnstr(expression: Expr) {
    freeVariables ++= variablesOf(expression)
    solver.assertCnstr(toZ3Formula(expression))
  }

  override def check: Option[Boolean] = solver.check()

  override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    freeVariables ++= assumptions.flatMap(variablesOf)
    solver.checkAssumptions(assumptions.toSeq.map(toZ3Formula(_)) : _*)
  }

  def getModel = {
    new Model(modelToMap(solver.getModel(), freeVariables.toSet))
  }

  def getUnsatCore = {
    solver.getUnsatCore().map(ast => fromZ3Formula(null, ast, BooleanType) match {
      case n @ Not(Variable(_)) => n
      case v @ Variable(_) => v
      case x => scala.sys.error("Impossible element extracted from core: " + ast + " (as Leon tree : " + x + ")")
    }).toSet
  }
}
