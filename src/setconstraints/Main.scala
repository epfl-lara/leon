package setconstraints

import Trees._
import purescala.Definitions.Program
import purescala.Definitions.AbstractClassDef
import purescala.Reporter
import purescala.Extensions.Analyser

class Main(reporter: Reporter) extends Analyser(reporter) {
  val description: String = "Analyser for advanced type inference based on set constraints"
  override val shortDescription = "Set constraints"

  def analyse(pgm: Program) : Unit = {

    val (cnstr, traits, constructors) = ConstraintsGenerator(pgm)
    reporter.info("The constraints are: " + PrettyPrinter(cnstr))
    val solvedSystem = Solver.solve(cnstr, constructors)
    reporter.info("The solved systems are: " + solvedSystem.map(sys => PrettyPrinter(And(sys))))
  }

}
