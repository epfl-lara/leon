/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Definitions._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._
import Witnesses._

case class SourceInfo(fd: FunDef,
                      pc: Expr,
                      source: Expr,
                      spec: Expr,
                      eb: ExamplesBank) {

  val problem = Problem.fromSourceInfo(this)
}

object SourceInfo {
  def extractFromProgram(ctx: LeonContext, prog: Program): List[SourceInfo] = {
    val functions = ctx.findOption(SharedOptions.optFunctions) map { _.toSet }

    def excludeByDefault(fd: FunDef): Boolean = {
      fd.annotations contains "library"
    }

    val fdFilter = {
      import OptionsHelpers._
      filterInclusive(functions.map(fdMatcher(prog)), Some(excludeByDefault _))
    }

    // Look for choose()
    val results = for (f <- prog.definedFunctions if f.body.isDefined && fdFilter(f);
                       ci <- extractFromFunction(ctx, prog, f)) yield {
      ci
    }

    results.sortBy(_.source.getPos)
  }

  def extractFromFunction(ctx: LeonContext, prog: Program, fd: FunDef): Seq[SourceInfo] = {

    val term = Terminating(fd.typed, fd.params.map(_.id.toVariable))

    val eFinder = new ExamplesFinder(ctx, prog)

    // We are synthesizing, so all examples are valid ones
    val functionEb = eFinder.extractFromFunDef(fd, partition = false)

    for ((ch, path) <- new ChooseCollectorWithPaths().traverse(fd.fullBody)) yield {
      val outerEb = if (path == BooleanLiteral(true)) {
        functionEb
      } else {
        ExamplesBank.empty
      }

      val ci = SourceInfo(fd, and(path, term), ch, ch.pred, outerEb)

      val pcEb = eFinder.generateForPC(ci.problem.as, path, 20)
      val chooseEb = eFinder.extractFromProblem(ci.problem)

      ci.copy(eb = (outerEb union chooseEb) union pcEb)
    }
  }
}
