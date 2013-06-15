/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package test
package termination

import leon.termination._

import org.scalatest.FunSuite

import java.io.File

import TestUtils._

class TerminationRegression extends FunSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : TerminationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],TerminationReport] =
    leon.plugin.ExtractionPhase andThen leon.SubtypingPhase andThen leon.termination.TerminationPhase

  private def mkTest(file : File, leonOptions: Seq[LeonOption], forError: Boolean)(block: Output=>Unit) = {
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
          verify    = false,
          termination = true
        ),
        options = leonOptions,
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
      "regression/termination/" + cat,
      _.endsWith(".scala"))

    for(f <- fs) {
      mkTest(f, Seq(), forError)(block)
    }
  }

  forEachFileIn("valid") { output =>
    val Output(report, reporter) = output
    val failures = report.results.collect { case (fd, guarantee) if !guarantee.isGuaranteed => fd }
    assert(failures.isEmpty, "Functions " + failures.map(_.id) + " should terminate")
    // can't say anything about error counts because of postcondition strengthening that might fail (normal behavior)
    // assert(reporter.errorCount === 0)
    assert(reporter.warningCount === 0)
  }

  forEachFileIn("looping") { output =>
    val Output(report, reporter) = output
    val looping = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("looping") }
    assert(looping.forall(_._2.isInstanceOf[LoopsGivenInputs]), "Functions " + looping.filter(!_._2.isInstanceOf[LoopsGivenInputs]).map(_._1.id) + " should loop")
    val calling = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("calling") }
    assert(calling.forall(_._2.isInstanceOf[CallsNonTerminating]), "Functions " + calling.filter(!_._2.isInstanceOf[CallsNonTerminating]).map(_._1.id) + " should call non-terminating")
    val ok = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("ok") }
    assert(ok.forall(_._2.isGuaranteed), "Functions " + ok.filter(!_._2.isGuaranteed).map(_._1.id) + " should terminate")
//    assert(reporter.errorCount >= looping.size + calling.size)
    assert(reporter.warningCount === 0)
  }

  forEachFileIn("unknown") { output =>
    val Output(report, reporter) = output
    val unknown = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("unknown") }
    assert(unknown.forall(_._2 == NoGuarantee), "Functions " + unknown.filter(_._2 != NoGuarantee).map(_._1.id) + " should be unknown")
    // can't say anything about error counts because of postcondition strengthening that might fail (normal behavior)
    // assert(reporter.errorCount === 0)
    assert(reporter.warningCount === 0)
  }

  forEachFileIn("error", true) { output => () }

}
