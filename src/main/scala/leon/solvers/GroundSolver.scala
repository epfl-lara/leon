/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import evaluators.DefaultEvaluator
import evaluators.EvaluationResults._
import purescala.Common.Identifier
import purescala.Definitions.Program
import purescala.Expressions.{BooleanLiteral, Expr}
import purescala.ExprOps.isGround
import purescala.Constructors.andJoin
import utils.Interruptible
import utils.IncrementalSeq

// This solver only "solves" ground terms by evaluating them
class GroundSolver(val context: LeonContext, val program: Program) extends Solver with NaiveAssumptionSolver {

  context.interruptManager.registerForInterrupts(this)

  val evaluator = new DefaultEvaluator(context, program)
  val dbg: Any => Unit = context.reporter.debug(_)

  def name: String = "ground"

  private val assertions = new IncrementalSeq[Expr]()

  // Ground terms will always have the empty model
  def getModel: Model = Model.empty

  def assertCnstr(expression: Expr): Unit = {
    assertions += expression
  }

  def check: Option[Boolean] = {
    val expr = andJoin(assertions.toSeq)

    if (isGround(expr)) {
      evaluator.eval(expr) match {
        case Successful(BooleanLiteral(result)) =>
          Some(result)
        case RuntimeError(message) =>
          dbg(s"Evaluation of $expr resulted in runtime error")
          Some(false)
        case _ =>
          dbg(s"Solver $name encountered error during evaluation.")
          None
      }
    } else {
      dbg(s"Non-ground expression $expr given to solver $name")
      None
    }
  }

  def free(): Unit = {
    assertions.clear()
  }

  def push() = {
    assertions.push()
  }

  def pop() = {
    assertions.pop()
  }

  def reset() = {
    assertions.reset()
  }

  def interrupt(): Unit = {}

  def recoverInterrupt(): Unit = {}
}
