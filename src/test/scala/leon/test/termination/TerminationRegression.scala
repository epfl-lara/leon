/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.termination

import leon._
import leon.test._

import leon.termination._

import java.io.File

class TerminationRegression extends LeonTestSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : TerminationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],TerminationReport] =
    leon.frontends.scalac.ExtractionPhase andThen leon.utils.PreprocessingPhase andThen leon.termination.TerminationPhase

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

      val ctx = testContext.copy(
        settings = Settings(
          synthesis = false,
          xlang     = false,
          verify    = false,
          termination = true
        ),
        options = leonOptions.toList,
        files = List(file)
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
    assert(looping.forall(p => p._2.isInstanceOf[LoopsGivenInputs] || p._2.isInstanceOf[CallsNonTerminating]),
      "Functions " + looping.filter(p => !p._2.isInstanceOf[LoopsGivenInputs] && !p._2.isInstanceOf[CallsNonTerminating]).map(_._1.id) + " should loop")
    val calling = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("calling") }
    assert(calling.forall(_._2.isInstanceOf[CallsNonTerminating]), "Functions " + calling.filter(!_._2.isInstanceOf[CallsNonTerminating]).map(_._1.id) + " should call non-terminating")
    val ok = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("ok") }
    assert(ok.forall(_._2.isGuaranteed), "Functions " + ok.filter(!_._2.isGuaranteed).map(_._1.id) + " should terminate")
//    assert(reporter.errorCount >= looping.size + calling.size)
    assert(reporter.warningCount === 0)
  }

  /*
  forEachFileIn("unknown") { output =>
    val Output(report, reporter) = output
    val unknown = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("unknown") }
    assert(unknown.forall(_._2 == NoGuarantee), "Functions " + unknown.filter(_._2 != NoGuarantee).map(_._1.id) + " should be unknown")
    // can't say anything about error counts because of postcondition strengthening that might fail (normal behavior)
    // assert(reporter.errorCount === 0)
    assert(reporter.warningCount === 0)
  }
  */

  //forEachFileIn("error", true) { output => () }

}
