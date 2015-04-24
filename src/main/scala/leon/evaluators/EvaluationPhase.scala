/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Definitions._
import purescala.DefOps._
import purescala.Expressions._

object EvaluationPhase extends LeonPhase[Program, Unit] {
  val name = "Evaluation"
  val description = "Evaluating ground functions"

  implicit val debugSection = utils.DebugSectionEvaluation

  def run(ctx: LeonContext)(program: Program): Unit = {
    val evalFuns: Option[Seq[String]] = ctx.findOption(SharedOptions.optFunctions)

    val reporter = ctx.reporter

    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(evalFuns.map(fdMatcher), None)
    }

    val toEvaluate = funDefsFromMain(program).toList.filter(_.params.size == 0).filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)

    if (toEvaluate.isEmpty) reporter.warning("No ground functions found with the given names")
    
    val eval = new DefaultEvaluator(ctx, program)
    for (fd <- toEvaluate) {
      reporter.info(s" - Evaluating ${fd.id}")
      val call = FunctionInvocation(fd.typedWithDef, Seq())
      eval.eval(call) match {
        case EvaluationResults.Successful(ex) =>
          reporter.info(s"  => $ex")
        case EvaluationResults.RuntimeError(msg) =>
          reporter.warning(s"  Runtime Error: $msg")
        case EvaluationResults.EvaluatorError(msg) =>
          reporter.warning(s"  Evaluator Error: $msg")
      }
    }
  }
}
