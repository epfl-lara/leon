/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import purescala.Definitions._
import evaluators._

trait EvaluatingSolver extends Solver {
  val context: LeonContext
  val program: Program

  val useCodeGen: Boolean

  lazy val evaluator: DeterministicEvaluator =
    if (useCodeGen) {
      new CodeGenEvaluator(context, program)
    } else {
      new DefaultEvaluator(context, program)
    }
}
