/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import leon.grammars._
import purescala.ExprOps._
import purescala.Definitions.Program
import purescala.Expressions.Expr
import purescala.Extractors.TopLevelAnds
import Witnesses.Hint

package object grammars {

  def default(sctx: SynthesisContext, p: Problem, extraHints: Seq[Expr] = Seq()): ExpressionGrammar = {
    val TopLevelAnds(ws) = p.ws
    val hints = ws.collect { case Hint(e) if formulaSize(e) >= 4 => e }
    val inputs = p.allAs.map(_.toVariable) ++ hints ++ extraHints
    if (sctx.settings.steUserDefinedGrammar) {
      val recCalls = {
        if (sctx.findOptionOrDefault(SynthesisPhase.optIntroRecCalls)) Empty()
        else SafeRecursiveCalls(sctx.program, p.ws, p.pc, Some(1))
      }
      Union(
        GenericUDGrammar(sctx.program, Some(sctx.functionContext), inputs), //p.allAs map (_.toVariable))
        recCalls
      )
    } else {
      val exclude = sctx.settings.functionsToIgnore
      val recCalls = {
        if (sctx.findOptionOrDefault(SynthesisPhase.optIntroRecCalls)) Empty()
        else SafeRecursiveCalls(sctx.program, p.ws, p.pc)
      }

      Union(
        BaseGrammar,
        Closures(3),
        Equalities,
        CaseClasses(sctx.program),
        Tuples(5),
        Sets(1),
        OneOf(inputs),
        Constants(sctx.functionContext.fullBody),
        FunctionCalls(sctx.program, sctx.functionContext, exclude),
        recCalls
      )
    }
  }

  def values(prog: Program): ExpressionGrammar = {
    Union(
      Literals,
      Closures(3),
      CaseClasses(prog),
      Generics(prog),
      Tuples(5),
      Sets(2)
    )
  }
}
