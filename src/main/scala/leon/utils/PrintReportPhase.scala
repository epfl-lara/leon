/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

/** Pretty-prints a [[Report]] */
case object PrintReportPhase extends UnitPhase[Report] {

  override val description: String = "Print a Leon report"
  override val name: String = "PrintReport"

  override def apply(ctx: LeonContext, rep: Report): Unit = {
    ctx.reporter.info(rep.summaryString)
  }

}
