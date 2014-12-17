/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Trees._
import purescala.TreeOps._
import purescala.DefOps._
import Witnesses._

case class ChooseInfo(ctx: LeonContext,
                      prog: Program,
                      fd: FunDef,
                      pc: Expr,
                      source: Expr,
                      ch: Choose,
                      settings: SynthesisSettings) {

  val problem     = Problem.fromChoose(ch, pc)
  val synthesizer = new Synthesizer(ctx, fd, prog, problem, settings)
}

object ChooseInfo {
  def extractFromProgram(ctx: LeonContext, prog: Program, options: SynthesisSettings): List[ChooseInfo] = {

    // Look for choose()
    val results = for (f <- prog.definedFunctions if f.body.isDefined;
                       ci <- extractFromFunction(ctx, prog, f, options)) yield {
      ci
    }

    results.sortBy(_.source.getPos)
  }

  def extractFromFunction(ctx: LeonContext, prog: Program, fd: FunDef, options: SynthesisSettings): Seq[ChooseInfo] = {

    val actualBody = and(fd.precondition.getOrElse(BooleanLiteral(true)), fd.body.get)
    val term = Terminating(fd.typedWithDef, fd.params.map(_.id.toVariable))

    for ((ch, path) <- new ChooseCollectorWithPaths().traverse(actualBody)) yield {
      ChooseInfo(ctx, prog, fd, and(path, term), ch, ch, options)
    }
  }
}
