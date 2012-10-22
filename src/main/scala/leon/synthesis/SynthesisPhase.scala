package leon
package synthesis

import purescala.Definitions.Program

class SynthesisPhase(reporter: Reporter) extends plugin.TransformationPhase {
  val name        = "Synthesis"
  val description = "Synthesis"

  def apply(program: Program): Program = {
    val quietReporter = new QuietReporter
    val solvers  = List(
      new TrivialSolver(quietReporter),
      new FairZ3Solver(quietReporter)
    )

    new Synthesizer(reporter, solvers).synthesizeAll(program)
  }
}
