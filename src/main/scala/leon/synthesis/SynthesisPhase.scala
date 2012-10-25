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

    val synth = new Synthesizer(ctx.reporter, solvers)
    val solutions = synth.synthesizeAll(p)

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
    val proc = Runtime.getRuntime().exec(program+" "+path)

    val errGobbler = new StreamGobbler(proc.getErrorStream(), System.err)
    val outGobbler = new StreamGobbler(proc.getInputStream(), System.out)
    val inGobbler  = new StreamGobbler(System.in, proc.getOutputStream())

    errGobbler.start()
    outGobbler.start()
    inGobbler.start()

    proc.waitFor()
    errGobbler.join()
    outGobbler.join()
  }

  import java.io.{InputStream, OutputStream}
  class StreamGobbler(is: InputStream, os: OutputStream) extends Thread {
    override def run() {
      var c: Int = is.read()
      while(c != 1) {
        os.write(c);
        os.flush();

        c = is.read()
      }
    }
  }
}
