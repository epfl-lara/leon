package purescala.testcases

import purescala.Reporter
import purescala.Trees._
import purescala.Definitions._
import purescala.Extensions._

class Main(reporter: Reporter) extends Analyser(reporter) {
  val description = "Testcase generation from preconditions"
  override val shortDescription = "testcases"

  def analyse(program : Program) : Unit = {
    // things that we could control with options:
    //   - generate for all functions or just impure
    //   - number of cases per function
    //   - do not generate for private functions (check FunDef.isPrivate)

    reporter.info("Running testcase generation...")

    // when you build the solver, call setProgram !
    reporter.info("Done.")
  }
}
