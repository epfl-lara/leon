package leon
package synthesis

import plugin.LeonContext
import purescala.Definitions.Program

object SynthesisPhase extends plugin.LeonPhase {
  val name        = "Synthesis"
  val description = "Synthesis"

  def run(ctx: LeonContext): LeonContext = {
    val quietReporter = new QuietReporter
    val solvers  = List(
      new TrivialSolver(quietReporter),
      new FairZ3Solver(quietReporter)
    )

    val newProgram = new Synthesizer(ctx.reporter, solvers).synthesizeAll(ctx.program)

    ctx.copy(program = newProgram)
  }
}
