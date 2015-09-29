/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.verification

import leon._
import leon.test._

import leon.verification.{AnalysisPhase, VerificationReport}
import leon.xlang.FixReportLabels
import leon.frontends.scalac.ExtractionPhase
import leon.utils.PreprocessingPhase

import _root_.smtlib.interpreters._

import java.io.File

class XLangVerificationSuite extends LeonRegressionSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : VerificationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],VerificationReport] =
    ExtractionPhase                             andThen
    new PreprocessingPhase(desugarXLang = true) andThen
    AnalysisPhase                               andThen
    FixReportLabels

  private def mkTest(file : File, leonOptions : Seq[String], forError: Boolean)(block: Output=>Unit) = {
    val fullName = file.getPath
    val start = fullName.indexOf("regression")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    val ignored = List(
      "regression/verification/xlang/valid/Nested15.scala"
    )

    val t = if (ignored.exists(displayName endsWith _)) {
      ignore _
    } else {
      test _
    }

    t(f"${nextInt()}%3d: $displayName ${leonOptions.mkString(" ")}", Nil) {
      assert(file.exists && file.isFile && file.canRead,
             s"Benchmark $displayName is not a readable file")

      val ctx = createLeonContext((file.getPath +: leonOptions) :_*)

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

    val isZ3Available = try {
      Z3Interpreter.buildDefault.free()
      true
    } catch {
      case e: java.io.IOException =>
        false
    }

       for(f <- fs) {
      mkTest(f, List(), forError)(block)
      mkTest(f, List("--feelinglucky"), forError)(block)
      if (isZ3Available) {
        mkTest(f, List("--solvers=smt-z3", "--feelinglucky"), forError)(block)
      }
    }
  }
  
  forEachFileIn("valid") { output =>
    val Output(report, reporter) = output
    assert(report.totalConditions === report.totalValid,
           "All verification conditions ("+report.totalConditions+") should be valid.")
    assert(reporter.errorCount === 0)
  }

  forEachFileIn("invalid") { output =>
    val Output(report, _) = output
    assert(report.totalInvalid > 0,
           "There should be at least one invalid verification condition.")
    assert(report.totalUnknown === 0,
           "There should not be unknown verification conditions.")
  }

}
