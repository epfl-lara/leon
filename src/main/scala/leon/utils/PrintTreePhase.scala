/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils


import purescala.Definitions.Program

case class PrintTreePhase(title: String) extends UnitPhase[Program] {

  val name = "Print program"
  val description = "Display: "+title

  def apply(ctx: LeonContext, p: Program) {
    ctx.reporter.info(ASCIIHelpers.title(title))
    ctx.reporter.info(p.asString(ctx))
  }
}
