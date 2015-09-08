package leon.isabelle

import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

import leon._
import leon.frontends.scalac.ExtractionPhase
import leon.purescala.Definitions._
import leon.utils._
import leon.solvers.isabelle._
import leon.test._
import leon.utils.PreprocessingPhase

class IsabelleLibrarySuite extends LeonRegressionSuite {

  object IsabelleNoopPhase extends LeonPhase[Program, Unit] {
    val name = "isabelle-noop"
    val description = "Isabelle definitions"

    implicit val debugSection = DebugSectionIsabelle

    def run(context: LeonContext)(program: Program): Unit =
      Await.result(IsabelleEnvironment(context, program).map(_ => ()), Duration.Inf)
  }

  test("Define the library") {
    val pipeline = ExtractionPhase andThen new PreprocessingPhase andThen IsabelleNoopPhase

    val ctx = Main.processOptions(Seq("--isabelle:download=true", "--functions=_")).copy(reporter = new TestSilentReporter())

    pipeline.run(ctx)(Nil)
  }

}
