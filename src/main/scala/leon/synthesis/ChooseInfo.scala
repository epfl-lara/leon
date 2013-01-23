package leon
package synthesis

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps.ChooseCollectorWithPaths

case class ChooseInfo(ctx: LeonContext,
                      prog: Program,
                      fd: FunDef,
                      pc: Expr,
                      ch: Choose,
                      options: SynthesisOptions) {

  val synthesizer = new Synthesizer(ctx, Some(fd), prog, Problem.fromChoose(ch), options)
  val problem     = Problem.fromChoose(ch, pc)
}

object ChooseInfo {
  def extractFromProgram(ctx: LeonContext, prog: Program, options: SynthesisOptions): List[ChooseInfo] = {
    def noop(u:Expr, u2: Expr) = u

    var results = List[ChooseInfo]()

    // Look for choose()
    for (f <- prog.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
      for ((ch, path) <- new ChooseCollectorWithPaths().traverse(f.body.get)) {
        results = ChooseInfo(ctx, prog, f, path, ch, options) :: results
      }
    }

    results.reverse
  }
}
