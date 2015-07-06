import leon._
import leon.synthesis._
import leon.synthesis.rules._
import leon.test._
import leon.utils._
import leon.frontends.scalac._

import org.scalameter.api._

class CegisPerfTest extends PerformanceTest.OfflineRegressionReport {

  override def persistor = new SerializationPersistor
  override def executor: Executor = LocalExecutor(warmer, aggregator, measurer)


  val lt = new LeonTestSuite{}

  val ctxPrograms = for (f <- lt.filesInResourceDir("regression/performance/cegis/", _.endsWith(".scala"))) yield {
    val extraction =
      ExtractionPhase andThen
      PreprocessingPhase

    val leonReporter = new TestSilentReporter

    val paths = List(f.getPath)
    val ctx = Main.processOptions(paths).copy(reporter = leonReporter,
                                                       interruptManager = new InterruptManager(leonReporter))

    (f.getName.dropRight(6), ctx, extraction.run(ctx)(paths))
  }

  val cegisRules = List(
    OnePoint,
    Ground,
    UnusedInput,
    EquivalentInputs,
    UnconstrainedOutput,
    CEGIS,
    Assert
  )

  val settings =  SynthesisSettings(timeoutMs = Some(20000), rules = cegisRules)

  performance of "CEGIS" in {
    for ((name, ctx, pgm) <- ctxPrograms) {
      measure.method(name) in {
        using(Gen.unit("test")) in { _ =>
          val cis = ChooseInfo.extractFromProgram(ctx, pgm).filterNot(_.fd.annotations("library"))
          for (ci <- cis) {
            val synth = new Synthesizer(ctx, pgm, ci, settings)
            val s = synth.getSearch
            val sols = s.search(synth.sctx)
          }
        }
      }
    }
  }

}
