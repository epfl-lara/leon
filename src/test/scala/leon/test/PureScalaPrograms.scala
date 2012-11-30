package leon
package test

import leon.verification.{AnalysisPhase,VerificationReport}

import org.scalatest.FunSuite

import java.io.File

class PureScalaPrograms extends FunSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : VerificationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],VerificationReport] =
    leon.plugin.ExtractionPhase andThen leon.verification.AnalysisPhase

  private def mkTest(file : File)(block: Output=>Unit) = {
    val fullName = file.getPath()
    val start = fullName.indexOf("regression")
    val displayName = file.getAbsolutePath()
/*
    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }
    */

    test("PureScala program %3d: [%s]".format(nextInt(), displayName)) {
      assert(file.exists && file.isFile && file.canRead,
             "Benchmark [%s] is not a readable file".format(displayName))

      val ctx = LeonContext(
        settings = Settings(
          synthesis = false,
          xlang     = false,
          verify    = true
        ),
        files = List(file),
        reporter = new SilentReporter
      )

      val pipeline = mkPipeline

      val report = pipeline.run(ctx)("--timeout=2" :: file.getPath :: Nil)

      block(Output(report, ctx.reporter))
    }
  }

  private def forEachFileIn(dirName : String)(block : Output=>Unit) {
    import scala.collection.JavaConversions._

    val dir = this.getClass.getClassLoader.getResource(dirName)

    if(dir == null || dir.getProtocol != "file") {
      assert(false, "Tests have to be run from within `sbt`, for otherwise " +
                    "the test files will be harder to access (and we dislike that).")
    }

    for(f <- (new File(dir.toURI())).listFiles() if f.getPath().endsWith(".scala")) {
      mkTest(f)(block)
    }
  }
  
  forEachFileIn("regression/verification/purescala/valid") { output =>
    val Output(report, reporter) = output
    assert(report.totalConditions === report.totalValid,
           "All verification conditions ("+report.totalConditions+") should be valid.")
    assert(reporter.errorCount === 0)
    assert(reporter.warningCount === 0)
  }

  forEachFileIn("regression/verification/purescala/invalid") { output =>
    val Output(report, reporter) = output
    assert(report.totalInvalid > 0,
           "There should be at least one invalid verification condition.")
    assert(report.totalUnknown === 0,
           "There should not be unknown verification conditions.")
    assert(reporter.errorCount >= report.totalInvalid)
    assert(reporter.warningCount === 0)
  }
}
