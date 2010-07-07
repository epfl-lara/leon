package setconstraints

import purescala.Extensions._
import purescala.Definitions._
import purescala.Trees._
import purescala.Reporter

class Main(reporter: Reporter) extends Analyser(reporter) {
  val description: String = "Analyser for advanced type inference based on set constraints"
  override val shortDescription = "Set constraints"

  def analyse(program: Program) : Unit = {
    reporter.info("Nothing to do in this analysis.")
  }
}
