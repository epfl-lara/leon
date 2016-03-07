/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Definitions._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._
import Witnesses._

case class SourceInfo(fd: FunDef, source: Expr, problem: Problem)

object SourceInfo {

  class ChooseCollectorWithPaths extends CollectorWithPaths[(Choose,Expr)] {
    def collect(e: Expr, path: Seq[Expr]) = e match {
      case c: Choose => Some(c -> and(path: _*))
      case _ => None
    }
  }

  def extractFromProgram(ctx: LeonContext, prog: Program): List[SourceInfo] = {
    val functions = ctx.findOption(GlobalOptions.optFunctions) map { _.toSet }

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

    if (results.isEmpty) {
      ctx.reporter.warning("No 'choose' found. Maybe the functions you chose do not exist?")
    }

    results.sortBy(_.source.getPos)
  }

  def extractFromFunction(ctx: LeonContext, prog: Program, fd: FunDef): Seq[SourceInfo] = {

    val term = Terminating(fd.applied)

    val eFinder = new ExamplesFinder(ctx, prog)

    // We are synthesizing, so all examples are valid ones
    val functionEb = eFinder.extractFromFunDef(fd, partition = false)

    for ((ch, path) <- new ChooseCollectorWithPaths().traverse(fd)) yield {
      val outerEb = if (path == BooleanLiteral(true)) {
        functionEb
      } else {
        ExamplesBank.empty
      }

      val p = Problem.fromSpec(ch.pred, and(path, term), outerEb, Some(fd))

      val pcEb = eFinder.generateForPC(p.as, path, 20)
      val chooseEb = eFinder.extractFromProblem(p)
      val eb = (outerEb union chooseEb) union pcEb

      val betterP = p.copy(eb = eb)

      SourceInfo(fd, ch, betterP)
    }
  }
}
