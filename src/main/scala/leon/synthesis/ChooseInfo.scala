/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Definitions._
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
    val fterm = prog.library.terminating.getOrElse(ctx.reporter.fatalError("No library ?!?"))

    var results = List[ChooseInfo]()

    // Look for choose()
    for (f <- prog.definedFunctions if f.body.isDefined) {
      val actualBody = And(f.precondition.getOrElse(BooleanLiteral(true)), f.body.get)
      val withinCall = FunctionInvocation(f.typedWithDef, f.params.map(_.id.toVariable))
      val term = FunctionInvocation(fterm.typed(Seq(f.returnType)), Seq(withinCall))

      for ((ch, path) <- new ChooseCollectorWithPaths().traverse(actualBody)) {
        results = ChooseInfo(ctx, prog, f, And(path, term), ch, ch, options) :: results
      }
    }

    results.sortBy(_.source.getPos)
  }
}
