/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.verification

import leon._
import leon.test._
import leon.frontends.scalac.ExtractionPhase
import leon.utils.PreprocessingPhase
import leon.verification.AnalysisPhase

class LibraryVerificationSuite extends LeonRegressionSuite {
  test("Verify the library") {
      val pipeline = ExtractionPhase    andThen
                     new PreprocessingPhase andThen
                     AnalysisPhase

      val ctx = Main.processOptions(Seq("--functions=_")).copy(reporter = new TestSilentReporter())

      val report = pipeline.run(ctx)(Nil)

      assert(report.totalConditions === report.totalValid, "Only "+report.totalValid+" valid out of "+report.totalConditions)
  }
}
