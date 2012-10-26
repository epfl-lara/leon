package leon
package synthesis

import purescala.Definitions.Program

object SynthesisPhase extends LeonPhase[Program, Program] {
  val name        = "Synthesis"
  val description = "Synthesis"

  def run(ctx: LeonContext)(p: Program): Program = {
    val quietReporter = new QuietReporter
    val solvers  = List(
      new TrivialSolver(quietReporter),
      new FairZ3Solver(quietReporter)
    )

    val synth = new Synthesizer(ctx.reporter, solvers)
    val solutions = synth.synthesizeAll(p)

    for (file <- ctx.files) {
      synth.updateFile(new java.io.File(file), solutions)
    }

    p
  }

}
