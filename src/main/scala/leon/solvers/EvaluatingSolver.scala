package leon
package solvers

import purescala.Definitions._
import evaluators._

trait EvaluatingSolver extends Solver {
  val context: LeonContext
  val program: Program

  val useCodeGen: Boolean

  lazy val evaluator: Evaluator =
    if (useCodeGen) {
      new CodeGenEvaluator(context, program)
    } else {
      new DefaultEvaluator(context, program)
    }
}
