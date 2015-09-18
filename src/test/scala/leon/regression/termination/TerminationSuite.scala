/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.termination

import leon._
import leon.test._

import leon.termination._

import java.io.File

class TerminationSuite extends LeonRegressionSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : TerminationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],TerminationReport] =
    leon.frontends.scalac.ExtractionPhase andThen
    new leon.utils.PreprocessingPhase     andThen
    leon.termination.TerminationPhase

  private def mkTest(file : File, leonOptions: Seq[LeonOption[Any]], forError: Boolean)(block: Output=>Unit) = {
    val fullName = file.getPath
    val start = fullName.indexOf("regression")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    val ignored = List(
      "verification/purescala/valid/MergeSort.scala",
      "verification/purescala/valid/InductiveQuantification.scala"
    )

    val t = if (ignored.exists(displayName endsWith _)) {
      ignore _
    } else {
      test _
    }

    t(f"${nextInt()}%3d: $displayName ${leonOptions.mkString(" ")}", Seq()) {
      assert(file.exists && file.isFile && file.canRead,
             s"Benchmark $displayName is not a readable file")

      val ctx = testContext.copy(
        options = leonOptions,
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

  private def forEachFileIn(files: Iterable[File], forError: Boolean = false)(block : Output=>Unit) {
    for(f <- files) {
      mkTest(f, Seq(), forError)(block)
    }
  }

  def validFiles = filesInResourceDir("regression/termination/valid",            _.endsWith(".scala")) ++
                   filesInResourceDir("regression/verification/purescala/valid", _.endsWith(".scala"))

  def loopingFiles = filesInResourceDir("regression/termination/looping", _.endsWith(".scala"))

  forEachFileIn(validFiles) { case Output(report, _) =>
    val failures = report.results.collect { case (fd, guarantee) if !guarantee.isGuaranteed => fd }
    assert(failures.isEmpty, "Functions " + failures.map(_.id) + " should terminate")
    // can't say anything about error counts because of postcondition strengthening that might fail (normal behavior)
    // assert(reporter.errorCount === 0)
    //assert(reporter.warningCount === 0)
  }

  forEachFileIn(loopingFiles) { case Output(report, _) =>
    val looping = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("looping") }
    val notLooping = looping.filterNot(p => p._2.isInstanceOf[NonTerminating] || p._2.isInstanceOf[CallsNonTerminating])
    assert(notLooping.isEmpty, "Functions " + notLooping.map(_._1.id) + " should loop")

    val calling = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("calling") }
    val notCalling = calling.filterNot(p => p._2.isInstanceOf[CallsNonTerminating])
    assert(notCalling.isEmpty, "Functions " + notCalling.map(_._1.id) + " should call non-terminating")

    val guar = report.results.filter { case (fd, guarantee) => fd.id.name.startsWith("ok") }
    val notGuaranteed = guar.filterNot(p => p._2.isGuaranteed)
    assert(notGuaranteed.isEmpty, "Functions " + notGuaranteed.map(_._1.id) + " should terminate")

//    assert(reporter.errorCount >= looping.size + calling.size)
    //assert(reporter.warningCount === 0)
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
