/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package repair

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Constructors._
import purescala.DefOps._

object RepairPhase extends LeonPhase[Program, Program] {
  val name = "Repair"
  val description = "Repairing"

  implicit val debugSection = utils.DebugSectionRepair

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2",   "Repair functions f1,f2,...")
  )

  def run(ctx: LeonContext)(program: Program): Program = {
    var repairFuns: Option[Seq[String]] = None
    var verifTimeout: Option[Long] = None

    val reporter = ctx.reporter

    for(opt <- ctx.options) opt match {
      case v @ LeonValueOption("timeout", _) =>
        verifTimeout = v.asLong(ctx)
      case LeonValueOption("functions", ListValue(fs)) =>
        repairFuns = Some(fs)
      case _ =>
    }


    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(repairFuns.map(fdMatcher), None)
    }

    val toRepair = funDefsFromMain(program).toList.sortWith((fd1, fd2) => fd1.getPos < fd2.getPos).filter(fdFilter)

    for (fd <- toRepair) {
      new Repairman(ctx, program, fd, verifTimeout).repair()
    }

    program
  }
}
