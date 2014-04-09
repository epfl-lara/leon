/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

case class ChooseInfo(ctx: LeonContext,
                      prog: Program,
                      fd: FunDef,
                      pc: Expr,
                      source: Expr,
                      ch: Choose,
                      options: SynthesisOptions) {

  val problem     = Problem.fromChoose(ch, pc)
  val synthesizer = new Synthesizer(ctx, Some(fd), prog, problem, options)
}

object ChooseInfo {
  def extractFromProgram(ctx: LeonContext, prog: Program, options: SynthesisOptions): List[ChooseInfo] = {
    def noop(u:Expr, u2: Expr) = u

    var results = List[ChooseInfo]()

    // Look for choose()
    for (f <- prog.definedFunctions if f.body.isDefined) {
      val actualBody = And(f.precondition.getOrElse(BooleanLiteral(true)), f.body.get)

      for ((ch, path) <- new ChooseCollectorWithPaths().traverse(actualBody)) {
        results = ChooseInfo(ctx, prog, f, path, ch, ch, options) :: results
      }
    }


    if (options.allSeeing) {
      // Functions that call holes are also considered for (all-seeing) synthesis

      val holesFd = prog.definedFunctions.filter(fd => fd.hasBody && containsHoles(fd.body.get)).toSet

      val callers = prog.callGraph.transitiveCallers(holesFd) ++ holesFd

      for (f <- callers if f.hasPostcondition && f.hasBody) {
        val path = f.precondition.getOrElse(BooleanLiteral(true))

        val x = FreshIdentifier("x", true).setType(f.returnType)
        val (pid, pex) = f.postcondition.get

        val ch = Choose(List(x), And(Equals(x.toVariable, f.body.get), replaceFromIDs(Map(pid -> x.toVariable), pex)))

        results = ChooseInfo(ctx, prog, f, path, f.body.get, ch, options) :: results
      }
    }

    results.sortBy(_.fd.id.toString)
  }
}
