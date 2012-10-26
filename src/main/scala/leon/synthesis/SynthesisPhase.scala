package leon
package synthesis

import solvers.TrivialSolver
import solvers.z3.FairZ3Solver

import purescala.Definitions.Program

object SynthesisPhase extends LeonPhase[Program, Program] {
  val name        = "Synthesis"
  val description = "Synthesis"

  override def definedOptions = Set(
    LeonFlagOptionDef("inplace", "--inplace", "Debug level")
  )

  def run(ctx: LeonContext)(p: Program): Program = {
    val quietReporter = new QuietReporter
    val solvers  = List(
      new TrivialSolver(quietReporter),
      new FairZ3Solver(quietReporter)
    )

    var inPlace = false
    for(opt <- ctx.options) opt match {
      case LeonFlagOption("inplace") =>
        inPlace = true
      case _ =>
    }

    val synth = new Synthesizer(ctx.reporter, solvers)
    val solutions = synth.synthesizeAll(p)

    if (inPlace) {
      for (file <- ctx.files) {
        synth.updateFile(new java.io.File(file), solutions)
      }
    }

    p
  }

}
