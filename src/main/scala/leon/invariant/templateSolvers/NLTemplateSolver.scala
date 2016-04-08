/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.templateSolvers

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import evaluators._
import java.io._
import solvers._
import solvers.combinators._
import solvers.smtlib._
import solvers.z3._
import scala.util.control.Breaks._
import purescala.ScalaPrinter
import scala.collection.mutable.{ Map => MutableMap }
import scala.reflect.runtime.universe
import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.util.ExpressionTransformer._
import invariant.structure._
import invariant.structure.FunctionUtils._
import Stats._

import Util._
import PredicateUtil._
import SolverUtil._

object NLTemplateSolver {
  val verbose = true
}

class NLTemplateSolver(ctx: InferenceContext, program: Program,
                       rootFun: FunDef, ctrTracker: ConstraintTracker,
                       minimizer: Option[(Expr, Model) => Model])
    extends TemplateSolver(ctx, rootFun, ctrTracker) {

  private val startFromEarlierModel = false
  // state for tracking the last model
  private var lastFoundModel: Option[Model] = None

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  override def solve(tempIds: Set[Identifier], funs: Seq[FunDef]): (Option[Model], Option[Set[Call]]) = {
    val initModel = completeModel(
      (if (this.startFromEarlierModel && lastFoundModel.isDefined) lastFoundModel.get
      else Model.empty), tempIds)
    val univSolver = new UniversalQuantificationSolver(ctx, program, funs, ctrTracker, minimizer)
    val (resModel, seenCalls) = univSolver.solveUNSAT(initModel, (m: Model) => lastFoundModel = Some(m))
    univSolver.free
    (resModel, seenCalls)
  }
}
