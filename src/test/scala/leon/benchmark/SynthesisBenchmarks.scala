package leon.benchmark

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.solvers.Solver
import leon.synthesis._
import leon.test.synthesis._

import java.io.File

object SynthesisBenchmarks extends App {

  private def forEachFileIn(dirName : String)(block : File=>Unit) {
    import scala.collection.JavaConversions._

    for(f <- (new File(dirName)).listFiles() if f.getPath().endsWith(".scala")) {
      block(f)
    }
  }

  val infoSep    : String = "╟" + ("┄" * 86) + "╢"
  val infoFooter : String = "╚" + ("═" * 86) + "╝"
  val infoHeader : String = ". ┌────────────┐\n" +
                            "╔═╡ Benchmarks ╞" + ("═" * 71) + "╗\n" +
                            "║ └────────────┘" + (" " * 71) + "║"

  def infoLine(file: String, f: String, ts: Long, nAlt: Int, nSuccess: Int, nInnap: Int, nDecomp: Int) : String = {
    "║ %-30s %-24s %3d %10s %10s ms ║".format(
      file,
      f,
      nAlt,
      nSuccess+"/"+nInnap+"/"+nDecomp,
      ts)
  }

  println(infoHeader)

  var nSuccessTotal, nInnapTotal, nDecompTotal, nAltTotal = 0
  var tTotal: Long = 0

  forEachFileIn("testcases/synthesis/") { file => 

    val ctx = LeonContext(
      settings = Settings(
        synthesis = true,
        xlang     = false,
        verify    = false
      ),
      files = List(file),
      reporter = new DefaultReporter
    )

    val opts = SynthesizerOptions()

    val pipeline = leon.plugin.ExtractionPhase andThen ExtractProblemsPhase

    val (results, solver) = pipeline.run(ctx)(file.getPath :: Nil)

    val sctx = SynthesisContext(solver, new SilentReporter)


    for ((f, ps) <- results; p <- ps) {
      val ts = System.currentTimeMillis

      val rr = rules.CEGIS.attemptToApplyOn(sctx, p)
      
      val nAlt = rr.alternatives.size
      var nSuccess, nInnap, nDecomp = 0

      for (alt <- rr.alternatives) {
        alt.apply() match {
          case RuleApplicationImpossible =>
            nInnap += 1
          case s: RuleDecomposed =>
            nDecomp += 1
          case s: RuleSuccess =>
            nSuccess += 1
        }
      }

      val t = System.currentTimeMillis - ts

      nAltTotal     += nAlt
      tTotal        += t
      nSuccessTotal += nSuccess
      nInnapTotal   += nInnap
      nDecompTotal  += nDecomp

      println(infoLine(file.getName().toString, f.id.toString, t, nAlt, nSuccess, nInnap, nDecomp))
    }

    println(infoSep)

  }

  println(infoLine("TOTAL", "", tTotal, nAltTotal, nSuccessTotal, nInnapTotal, nDecompTotal))

  println(infoFooter)
}
