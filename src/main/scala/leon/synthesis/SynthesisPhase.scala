package leon
package synthesis

import purescala.Definitions.Program

object SynthesisPhase extends TransformationPhase {
  val name        = "Synthesis"
  val description = "Synthesis"

  def apply(ctx: LeonContext, p: Program): Program = {
    val quietReporter = new QuietReporter
    val solvers  = List(
      new TrivialSolver(quietReporter),
      new FairZ3Solver(quietReporter)
    )

    new Synthesizer(ctx.reporter, solvers).synthesizeAll(p)
  }
}
