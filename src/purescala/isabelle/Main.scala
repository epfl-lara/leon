package purescala.isabelle

import purescala.Reporter
import purescala.Trees._
import purescala.Definitions._
import purescala.Extensions._
import purescala.Settings
import purescala.Common.Identifier

class Main(reporter : Reporter) extends Analyser(reporter) {
  val description = "Generates Isabelle source"
  override val shortDescription = "isabelle"

  def analyse(program : Program) : Unit = {
    reporter.info(program)
    reporter.info("Done with Isabelle translation.")
  }

}
