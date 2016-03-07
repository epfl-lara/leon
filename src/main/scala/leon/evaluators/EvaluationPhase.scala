/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import leon.Main.MainComponent
import purescala.Definitions._
import purescala.DefOps._
import purescala.Expressions._

object EvaluationPhase extends UnitPhase[Program] {
  val name = "Evaluation"
  val description = "Evaluating ground functions"

  implicit val debugSection = utils.DebugSectionEvaluation

  def apply(ctx: LeonContext, program: Program): Unit = {
    val evalFuns: Option[Seq[String]] = ctx.findOption(GlobalOptions.optFunctions)

    val evaluator = ctx.findOptionOrDefault(MainComponent.optEval)

    val reporter = ctx.reporter

    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(evalFuns.map(fdMatcher(program)), None)
    }

    val toEvaluate = funDefsFromMain(program).toList.filter(_.params.size == 0).filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)

    if (toEvaluate.isEmpty) reporter.warning("No ground functions found with the given names")

    val eval = if (evaluator == "codegen") {
      new CodeGenEvaluator(ctx, program)
    } else if (evaluator == "default" || evaluator == "") {
      new DefaultEvaluator(ctx, program)
    } else {
      reporter.fatalError(s"Unknown evaluator '$evaluator'. Available: default, codegen")
    }

    for (fd <- toEvaluate) {
      reporter.info(s" - Evaluating ${fd.id}")
      val call = FunctionInvocation(fd.typed, Seq())
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
