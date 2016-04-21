/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import evaluators.DefaultEvaluator
import purescala.Path
import purescala.Definitions.Program
import purescala.Extractors.TopLevelAnds
import purescala.Expressions._
import purescala.Constructors._
import purescala.Common._
import Witnesses.Terminating
import utils.Helpers.terminatingCalls

case object IntroduceRecCalls extends NormalizingRule("Introduce rec. calls") {

  private class NoChooseEvaluator(ctx: LeonContext, prog: Program) extends DefaultEvaluator(ctx, prog) {
    override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
      case ch: Choose =>
        throw EvalError("Encountered choose!")
      case _ =>
        super.e(expr)
    }
  }

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val existingCalls = p.pc.bindings.collect { case (_, fi: FunctionInvocation) => fi }.toSet

    val calls = terminatingCalls(hctx.program, p.ws, p.pc, None, false)
      .map(_._1).distinct.filterNot(existingCalls)

    if (calls.isEmpty) return Nil

    val specifyCalls = hctx.findOptionOrDefault(SynthesisPhase.optSpecifyRecCalls)

    val recs = calls.map { newCall =>
      val rec = FreshIdentifier("rec", newCall.getType, alwaysShowUniqueID = true)

      // Assume the postcondition of recursive call
      val path = if (specifyCalls) {
        Path.empty withBinding (rec -> newCall)
      } else {
        Path(application(
          newCall.tfd.withParamSubst(newCall.args, newCall.tfd.postOrTrue),
          Seq(rec.toVariable)
        ))
      }

      (rec, path)
    }

    val onSuccess = forwardMap(letTuple(recs.map(_._1), tupleWrap(calls), _))

    List(new RuleInstantiation(s"Introduce calls ${calls mkString ", "}", SolutionBuilderDecomp(List(p.outType), onSuccess)) {

      def apply(nohctx: SearchContext): RuleApplication = {

        val psol = new PartialSolution(hctx.search.strat, true)
          .solutionAround(hctx.currentNode)(Error(p.outType, "Encountered choose!"))
          .getOrElse(hctx.reporter.fatalError("Unable to get outer solution"))
          .term

        val origImpl = hctx.functionContext.fullBody
        hctx.functionContext.fullBody = psol

        //val evaluator = new NoChooseEvaluator(hctx, hctx.program)

        val newWs = calls map Terminating
        val TopLevelAnds(ws) = p.ws
        try {
          val newProblem = p.copy(
            as = p.as ++ (if (specifyCalls) Nil else recs.map(_._1)),
            pc = recs.map(_._2).foldLeft(p.pc)(_ merge _),
            ws = andJoin(ws ++ newWs),
            eb = p.eb
          )

          RuleExpanded(List(newProblem))
        } finally {
          hctx.functionContext.fullBody = origImpl
        }
      }
    })

  }
}
