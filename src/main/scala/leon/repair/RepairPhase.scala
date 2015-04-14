/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package repair

import purescala.Definitions._
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
    var verifTimeoutMs: Option[Long] = None

    val reporter = ctx.reporter

    for(opt <- ctx.options) opt match {
      case v @ LeonValueOption("timeout", _) =>
        verifTimeoutMs = v.asLong(ctx) map { _ * 1000L }
      case LeonValueOption("functions", ListValue(fs)) =>
        repairFuns = Some(fs)
      case _ =>
    }


    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(repairFuns.map(fdMatcher), None)
    }

    val toRepair = funDefsFromMain(program).toList.filter(fdFilter).filter{ _.hasPostcondition }.sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)

    if (toRepair.isEmpty) reporter.warning("No functions found with the given names")
    
    for (fd <- toRepair) {
      val rep = new Repairman(ctx, program, fd, verifTimeoutMs, verifTimeoutMs)
      rep.repair()
    }

    program
  }
}
