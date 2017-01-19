/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import leon.grammars._
import purescala.ExprOps._
import purescala.Expressions.Expr
import purescala.Extractors.TopLevelAnds
import purescala.Types.{BooleanType, Int32Type, IntegerType}
import Witnesses.Hint

package object grammars {

  def default(sctx: SynthesisContext, p: Problem, extraHints: Seq[Expr] = Seq()): ExpressionGrammar = {
    val TopLevelAnds(ws) = p.ws
    val hints = ws.collect { case Hint(e) if formulaSize(e) >= 4 => e }
    val inputs = p.allAs.map(_.toVariable) ++ hints ++ extraHints
    if (sctx.settings.steUserDefinedGrammar) {
      GenericUDGrammar(sctx, sctx.program, Some(sctx.functionContext), p.allAs)
    } else {
      val exclude = sctx.settings.functionsToIgnore
      val recCalls = {
        if (sctx.findOptionOrDefault(SynthesisPhase.optIntroduceRecCalls)) Empty()
        else SafeRecursiveCalls(sctx.program, p.ws, p.pc)
      }

      Union(Seq(
        BaseGrammar,
        Closures,
        EqualityGrammar(Set(IntegerType, Int32Type, BooleanType) ++ inputs.map { _.getType }),
        OneOf(inputs),
        Constants(sctx.functionContext.fullBody),
        FunctionCalls(sctx.program, sctx.functionContext, inputs.map(_.getType), exclude),
        recCalls
      ))
    }
  }
}
