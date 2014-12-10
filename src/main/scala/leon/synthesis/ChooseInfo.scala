/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Trees._
import purescala.TreeOps._
import purescala.DefOps._

case class ChooseInfo(ctx: LeonContext,
                      prog: Program,
                      fd: FunDef,
                      pc: Expr,
                      source: Expr,
                      ch: Choose,
                      options: SynthesisOptions) {

  val problem     = Problem.fromChoose(ch, pc)
  val synthesizer = new Synthesizer(ctx, fd, prog, problem, options)
}

object ChooseInfo {
  def extractFromProgram(ctx: LeonContext, prog: Program, options: SynthesisOptions): List[ChooseInfo] = {

    // Look for choose()
    val results = for (f <- prog.definedFunctions if f.body.isDefined;
                       ci <- extractFromFunction(ctx, prog, f, options)) yield {
      ci
    }

    results.sortBy(_.source.getPos)
  }

  def extractFromFunction(ctx: LeonContext, prog: Program, fd: FunDef, options: SynthesisOptions): Seq[ChooseInfo] = {
    val fterm = prog.library.terminating.getOrElse(ctx.reporter.fatalError("No library ?!?"))

    val actualBody = and(fd.precondition.getOrElse(BooleanLiteral(true)), fd.body.get)
    val withinCall = FunctionInvocation(fd.typedWithDef, fd.params.map(_.id.toVariable))
    val term = FunctionInvocation(fterm.typed(Seq(fd.returnType)), Seq(withinCall))

    for ((ch, path) <- new ChooseCollectorWithPaths().traverse(actualBody)) yield {
      ChooseInfo(ctx, prog, fd, and(path, term), ch, ch, options)
    }
  }
}
