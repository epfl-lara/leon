package setconstraints

import purescala.Definitions.Program
import purescala.Reporter
import purescala.Extensions.Analyser

class Main(reporter: Reporter) extends Analyser(reporter) {
  val description: String = "Analyser for advanced type inference based on set constraints"
  override val shortDescription = "Set constraints"

  def analyse(pgm: Program) : Unit = {

    val (tpeVars, funVars) = LabelProgram(pgm)
    val cl2adt = ADTExtractor(pgm)

    val cnstr = CnstrtGen(pgm, tpeVars, funVars, cl2adt)

    reporter.info(tpeVars.toString)
    reporter.info(funVars.toString)
    reporter.info(cl2adt.toString)

    reporter.info("THE CONSTRAINTS")
    reporter.info(PrettyPrinter(cnstr))

  }

}
