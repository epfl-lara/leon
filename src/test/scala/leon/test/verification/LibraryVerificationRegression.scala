/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package test
package verification

import java.io.File

class LibraryVerificationRegression extends LeonTestSuite {
  test("Verify the library") {
      val pipeline = leon.frontends.scalac.ExtractionPhase andThen
                     leon.purescala.MethodLifting andThen
                     leon.utils.TypingPhase andThen
                     leon.purescala.CompleteAbstractDefinitions andThen
                     leon.verification.AnalysisPhase

      val ctx = Main.processOptions(Seq("--library", "--functions=_")).copy(reporter = new TestSilentReporter())

      val report = pipeline.run(ctx)(Nil)

      assert(report.totalConditions === report.totalValid, "Only "+report.totalValid+" valid out of "+report.totalConditions);
  }
}
