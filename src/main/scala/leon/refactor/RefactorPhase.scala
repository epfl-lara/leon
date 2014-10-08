/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package refactor

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Constructors._
import purescala.DefOps._

object RefactorPhase extends LeonPhase[Program, Program] {
  val name = "Refactor"
  val description = "Refactoring/Repairing"

  implicit val debugSection = utils.DebugSectionRefactor

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2",   "Refactor functions f1,f2,...")
  )

  def run(ctx: LeonContext)(program: Program): Program = {
    var refactorFuns: Option[Seq[String]] = None

    val reporter = ctx.reporter

    for(opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        refactorFuns = Some(fs)
      case _ =>
    }


    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(refactorFuns.map(fdMatcher), None)
    }

    val toRefactor = funDefsFromMain(program).toList.sortWith((fd1, fd2) => fd1.getPos < fd2.getPos).filter(fdFilter)

    for (fd <- toRefactor) {
      new Repairman(ctx, program, fd).repair()
    }

    program
  }
}
