package leon
package synthesis

import purescala.Definitions.Program

class SynthesisPhase(reporter: Reporter) extends plugin.TransformationPhase {
  val name        = "Synthesis"
  val description = "Synthesis"

  def apply(program: Program): Program = {
    val solvers  = List(
      new TrivialSolver(reporter),
      new FairZ3Solver(reporter)
    )

    new Synthesizer(reporter, solvers).synthesizeAll(program)
  }
}
