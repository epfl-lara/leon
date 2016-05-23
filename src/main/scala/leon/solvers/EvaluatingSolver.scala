/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import purescala.Definitions._
import evaluators._

trait EvaluatingSolver extends Solver {
  val program: Program

  val useCodeGen: Boolean

  val evaluator: DeterministicEvaluator = if (useCodeGen) {
    new CodeGenEvaluator(context, program, sctx.bank)
  } else {
    new DefaultEvaluator(context, program, sctx.bank)
  }
}

