package leon
package synthesis

import purescala.Definitions.Program

object SynthesisPhase extends LeonPhase[Program, PipelineControl] {
  val name        = "Synthesis"
  val description = "Synthesis"

  def run(ctx: LeonContext)(p: Program): PipelineControl = {
    val quietReporter = new QuietReporter
    val solvers  = List(
      new TrivialSolver(quietReporter),
      new FairZ3Solver(quietReporter)
    )

    val newProgram = new Synthesizer(ctx.reporter, solvers).synthesizeAll(p)

    detectEditor match {
      case Some(program) => 
        openEditor(program, "/home/ekneuss/plop")
        PipelineControl(restart = false)
      case None =>
        ctx.reporter.fatalError("Cannot open editor, $EDITOR / $VISUAL missing")
        PipelineControl(restart = false)
    }
  }

  def detectEditor: Option[String] = {
    Option(System.getenv("EDITOR")) orElse Option(System.getenv("VISUAL"))
  }

  def openEditor(program: String, path: String) {
    val p = sys.process.Process(program+" "+path)
    p !<
  }
}
