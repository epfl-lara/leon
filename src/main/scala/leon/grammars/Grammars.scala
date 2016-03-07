/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import synthesis.Witnesses.Hint
import purescala.Expressions._
import purescala.Definitions._
import purescala.Types._
import purescala.TypeOps._
import purescala.Extractors.TopLevelAnds
import purescala.ExprOps.formulaSize

import synthesis.{SynthesisContext, Problem}

object Grammars {

  def default(prog: Program, inputs: Seq[Expr], currentFunction: FunDef, exclude: Set[FunDef]): ExpressionGrammar[TypeTree] = {
    BaseGrammar ||
    EqualityGrammar(Set(IntegerType, Int32Type, BooleanType) ++ inputs.map { _.getType }) ||
    OneOf(inputs) ||
    Constants(currentFunction.fullBody) ||
    // SafeRecursiveCalls(prog, ws, pc) ||
    FunctionCalls(prog, currentFunction, inputs.map(_.getType), exclude)
  }

  def default(sctx: SynthesisContext, p: Problem, extraHints: Seq[Expr] = Seq()): ExpressionGrammar[TypeTree] = {
    val TopLevelAnds(ws) = p.ws
    val hints = ws.collect{ case Hint(e) if formulaSize(e) >= 4 => e }
    default(sctx.program, p.as.map(_.toVariable) ++ hints ++ extraHints, sctx.functionContext, sctx.settings.functionsToIgnore)
  }

  def typeDepthBound[T <: Typed](g: ExpressionGrammar[T], b: Int) = {
    g.filter(g => g.subTrees.forall(t => typeDepth(t.getType) <= b))
  }
}

