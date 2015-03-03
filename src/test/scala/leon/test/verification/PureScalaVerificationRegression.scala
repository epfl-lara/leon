/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.verification

import leon._
import leon.test._

import leon.verification.{AnalysisPhase,VerificationReport}

import leon.frontends.scalac.ExtractionPhase
import leon.utils.PreprocessingPhase

import _root_.smtlib.interpreters._

import java.io.File

class PureScalaVerificationRegression extends LeonTestSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : VerificationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String], VerificationReport] =
    ExtractionPhase                andThen
    PreprocessingPhase             andThen
    xlang.NoXLangFeaturesChecking  andThen
    AnalysisPhase

  private def mkTest(file : File, leonOptions : Seq[String], forError: Boolean)(block: Output=>Unit) = {
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
      "regression/verification/purescala/" + cat,
      _.endsWith(".scala"))

    val isZ3Available = try {
      new Z3Interpreter()
      true
    } catch {
      case e: java.io.IOException =>
        false
    }

    val isCVC4Available = try {
      new CVC4Interpreter()
      // @EK: CVC4 works on most testcases already, but not all and thus cannot be used in regression.
      true
    } catch {
      case e: java.io.IOException =>
        false
    }

    for(f <- fs) {
      mkTest(f, List("--feelinglucky"), forError)(block)
      mkTest(f, List("--codegen", "--evalground", "--feelinglucky"), forError)(block)
      mkTest(f, List("--solvers=fairz3,enum", "--codegen", "--evalground", "--feelinglucky"), forError)(block)
      if (isZ3Available) {
        mkTest(f, List("--solvers=smt-z3", "--feelinglucky"), forError)(block)
      }
      if (isCVC4Available) {
        mkTest(f, List("--solvers=smt-cvc4", "--feelinglucky"), forError)(block)
      }
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
