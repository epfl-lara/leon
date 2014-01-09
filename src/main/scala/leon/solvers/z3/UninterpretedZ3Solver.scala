/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers.z3

import z3.scala._

import leon.solvers._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._

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
  val precondition = BooleanLiteral(true)
  val grounder = None

  // this is fixed
  protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )
  toggleWarningMessages(true)

  initZ3()

  def push() {
    solver.push
  }

  def pop(lvl: Int = 1) {
    solver.pop(lvl)
  }

  private var variables = Set[Identifier]()
  private var containsFunCalls = false

  override protected[leon] def restartZ3(asserted: Seq[Expr]) {
    variables = Set.empty
    containsFunCalls = false
    super.restartZ3(asserted)
  }

  protected def assertZ3Cnstr(expression: Expr) {
    variables ++= variablesOf(expression)
    containsFunCalls ||= containsFunctionCalls(expression)
    solver.assertCnstr(toZ3Formula(expression).get)
  }

  def innerCheck: Option[Boolean] = {
    solver.check match {
      case Some(true) =>
        if (containsFunCalls) {
          None
        } else {
          Some(true)
        }

      case r =>
        r
    }
  }

  def innerCheckAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    variables ++= assumptions.flatMap(variablesOf(_))
    solver.checkAssumptions(assumptions.toSeq.map(toZ3Formula(_).get) : _*)
  }

  def getModel = {
    modelToMap(solver.getModel, variables)
  }

  def getUnsatCore = {
    solver.getUnsatCore.map(ast => fromZ3Formula(null, ast, None) match {
      case n @ Not(Variable(_)) => n
      case v @ Variable(_) => v
      case x => scala.sys.error("Impossible element extracted from core: " + ast + " (as Leon tree : " + x + ")")
    }).toSet
  }
}
