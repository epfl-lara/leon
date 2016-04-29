/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import purescala.Definitions._
import evaluators._

trait EvaluatingSolver extends Solver {
  val context: LeonContext
  val program: Program

  val useCodeGen: Boolean

  private var _bank: EvaluationBank = new EvaluationBank
  private var _evaluator: DeterministicEvaluator = _

  def evaluator: DeterministicEvaluator = {
    if (_evaluator eq null) _evaluator = if (useCodeGen) {
      new CodeGenEvaluator(context, program, bank)
    } else {
      new DefaultEvaluator(context, program, bank)
    }
    _evaluator
  }

  def bank: EvaluationBank = _bank
  def setBank(bank: EvaluationBank): this.type = {
    _bank = bank
    _evaluator = null
    this
  }
}

