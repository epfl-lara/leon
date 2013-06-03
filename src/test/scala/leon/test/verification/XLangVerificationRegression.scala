/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package test
package verification

import leon.verification.{AnalysisPhase,VerificationReport}

import org.scalatest.FunSuite

import java.io.File

import TestUtils._

class XLangVerificationRegression extends FunSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : VerificationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],VerificationReport] =
    leon.plugin.ExtractionPhase andThen leon.SubtypingPhase andThen xlang.XlangAnalysisPhase

  private def mkTest(file : File, forError: Boolean = false)(block: Output=>Unit) = {
    val fullName = file.getPath()
    val start = fullName.indexOf("regression")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    test("%3d: %s".format(nextInt(), displayName)) {
      assert(file.exists && file.isFile && file.canRead,
             "Benchmark %s is not a readable file".format(displayName))

      // println("testing " + displayName)

      val ctx = LeonContext(
        settings = Settings(
          synthesis = false,
          xlang     = false,
          verify    = true
        ),
        //options = List(LeonFlagOption("feelinglucky")),
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
      "regression/verification/xlang/" + cat,
      _.endsWith(".scala"))

    for(f <- fs) {
      mkTest(f, forError)(block)
    }
  }
  
  forEachFileIn("valid") { output =>
    val Output(report, reporter) = output
    assert(report.totalConditions === report.totalValid,
           "All verification conditions ("+report.totalConditions+") should be valid.")
    assert(reporter.errorCount === 0)
  }

  forEachFileIn("invalid") { output =>
    val Output(report, reporter) = output
    assert(report.totalInvalid > 0,
           "There should be at least one invalid verification condition.")
    assert(report.totalUnknown === 0,
           "There should not be unknown verification conditions.")
    assert(reporter.errorCount >= report.totalInvalid)
  }

  forEachFileIn("error", true) { output => () }

}
