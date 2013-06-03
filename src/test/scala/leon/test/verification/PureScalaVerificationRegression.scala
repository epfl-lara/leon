/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package test
package verification

import leon.verification.{AnalysisPhase,VerificationReport}

import org.scalatest.FunSuite

import java.io.File

import TestUtils._

class PureScalaVerificationRegression extends FunSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : VerificationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],VerificationReport] =
    leon.plugin.ExtractionPhase andThen leon.SubtypingPhase andThen leon.verification.AnalysisPhase

  private def mkTest(file : File, leonOptions : Seq[LeonOption], forError: Boolean)(block: Output=>Unit) = {
    val fullName = file.getPath()
    val start = fullName.indexOf("regression")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    test("%3d: %s %s".format(nextInt(), displayName, leonOptions.mkString(" "))) {
      assert(file.exists && file.isFile && file.canRead,
             "Benchmark %s is not a readable file".format(displayName))

      val ctx = LeonContext(
        settings = Settings(
          synthesis = false,
          xlang     = false,
          verify    = true
        ),
        options = leonOptions.toList,
        files = List(file),
        reporter = new SilentReporter
      )

      val pipeline = mkPipeline

      if(forError) {
        intercept[LeonFatalError]{
          pipeline.run(ctx)(file.getPath :: Nil)
        }
      } else {

        val report = pipeline.run(ctx)(file.getPath :: Nil)

        block(Output(report, ctx.reporter))
      }
    }
  }

  private def forEachFileIn(cat : String, forError: Boolean = false)(block : Output=>Unit) {
    val fs = filesInResourceDir(
      "regression/verification/purescala/" + cat,
      _.endsWith(".scala"))

    for(f <- fs) {
      mkTest(f, List(LeonFlagOption("feelinglucky")), forError)(block)
      mkTest(f, List(LeonFlagOption("codegen"), LeonFlagOption("evalground"), LeonFlagOption("feelinglucky")), forError)(block)
    }
  }
  
  forEachFileIn("valid") { output =>
    val Output(report, reporter) = output
    assert(report.totalConditions === report.totalValid,
           "All verification conditions ("+report.totalConditions+") should be valid.")
    assert(reporter.errorCount === 0)
    assert(reporter.warningCount === 0)
  }

  forEachFileIn("invalid") { output =>
    val Output(report, reporter) = output
    assert(report.totalInvalid > 0,
           "There should be at least one invalid verification condition.")
    assert(report.totalUnknown === 0,
           "There should not be unknown verification conditions.")
    assert(reporter.errorCount >= report.totalInvalid)
    assert(reporter.warningCount === 0)
  }
  forEachFileIn("error", true) { output => () }

}
