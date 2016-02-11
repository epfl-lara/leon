/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import evaluators.DefaultEvaluator
import purescala.Definitions.Program
import purescala.Extractors.TopLevelAnds
import purescala.Expressions._
import purescala.Constructors._
import purescala.Common._
import Witnesses.Terminating
import utils.Helpers.terminatingCalls

case object IntroduceRecCall extends Rule("Introduce rec. calls") {

  private class NoChooseEvaluator(ctx: LeonContext, prog: Program) extends DefaultEvaluator(ctx, prog) {
    override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
      case ch: Choose =>
        throw EvalError("Encountered choose!")
      case _ =>
        super.e(expr)
    }
  }

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val evaluator = new NoChooseEvaluator(hctxToCtx, hctx.program)

    val calls = terminatingCalls(hctx.program, p.ws, p.pc, None, false)

    calls.map { case (newCall, _) =>
      val rec = FreshIdentifier("rec", newCall.getType, alwaysShowUniqueID = true)

      val newWs = {
        val TopLevelAnds(ws) = p.ws
        andJoin(ws map {
          case Terminating(tfd, _) if tfd == newCall.tfd =>
            Terminating(tfd, newCall.args)
          case other =>
            other
        })
      }

      // Assume the postcondition of recursive call
      val post = application(
        newCall.tfd.withParamSubst(newCall.args, newCall.tfd.postOrTrue),
        Seq(rec.toVariable)
      )

      val onSuccess = forwardMap(Let(rec, newCall, _))

      new RuleInstantiation(s"Introduce recursive call $newCall", SolutionBuilderDecomp(List(p.outType), onSuccess)) {

        def apply(nohctx: SearchContext) = {

          val psol = new PartialSolution(hctx.search.g, true)
            .solutionAround(hctx.currentNode)(Error(p.outType, "Encountered choose!"))
            .getOrElse(hctx.sctx.context.reporter.fatalError("Unable to get outer solution"))
            .term

          val origImpl = hctx.sctx.functionContext.fullBody
          hctx.sctx.functionContext.fullBody = psol

          def mapExample(e: Example): List[Example] = {
            val res = evaluator.eval(newCall, p.as.zip(e.ins).toMap)
            res.result.toList map { e match {
              case InExample(ins) =>
                v => InExample(ins :+ v)
              case InOutExample(ins, outs) =>
                v => InOutExample(ins :+ v, outs)
            }}
          }

          val newProblem = p.copy(
            as = p.as :+ rec,
            pc = and(p.pc, post),
            ws = newWs,
            eb = p.eb.map(mapExample)
          )

          hctx.sctx.functionContext.fullBody = origImpl

          RuleExpanded(List(newProblem))
        }
      }

    }
  }
}
