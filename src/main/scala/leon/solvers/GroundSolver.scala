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

// This solver only "solves" ground terms by evaluating them
class GroundSolver(val context: LeonContext, val program: Program) extends Solver with Interruptible {

  context.interruptManager.registerForInterrupts(this)

  val evaluator = new DefaultEvaluator(context, program)
  val dbg: Any => Unit = context.reporter.debug(_)

  def name: String = "ground"

  private var assertions: List[Expr] = Nil

  // Ground terms will always have the empty model
  def getModel: Map[Identifier, Expr] = Map()

  def assertCnstr(expression: Expr): Unit = assertions ::= expression

  def check: Option[Boolean] = {
    val expr = andJoin(assertions)

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

  def free(): Unit = assertions = Nil

  def interrupt(): Unit = {}

  def recoverInterrupt(): Unit = {}
}
