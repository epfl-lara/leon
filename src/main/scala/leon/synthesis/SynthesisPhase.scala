package leon
package synthesis

import purescala.Definitions.Program

object SynthesisPhase extends LeonPhase {
  val name        = "Synthesis"
  val description = "Synthesis"

  def run(ctx: LeonContext): LeonContext = {
    val quietReporter = new QuietReporter
    val solvers  = List(
      new TrivialSolver(quietReporter),
      new FairZ3Solver(quietReporter)
    )

    val newProgram = new Synthesizer(ctx.reporter, solvers).synthesizeAll(ctx.program.get)

    ctx.copy(program = Some(newProgram))
  }
}
