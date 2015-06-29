/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.testcases

import leon._
import org.scalatest.time.SpanSugar._
import test.LeonTestSuite
import java.io.File
import org.scalatest.ParallelTestExecution

class TestCasesCompile extends LeonTestSuite {
  // Hard-code output directory, for Eclipse purposes

  val pipeline = frontends.scalac.ExtractionPhase andThen utils.PreprocessingPhase

  def testFrontend(f: File, strip: Int) = {
    val name = f.getAbsolutePath.split("/").toList.drop(strip).mkString("/")

    val ctx = createLeonContext()

    try {
      pipeline.run(ctx)(List(f.getAbsolutePath))
      info(name)
    } catch {
      case _: LeonFatalError =>
        fail("Failed to compile "+name)
    }
  }

  private def filesIn(path : String): Seq[File] = {
    val fs = filesInResourceDir(path, _.endsWith(".scala"), recursive=true)

    fs.toSeq
  }

  val baseDir = "regression/testcases/"

  val slashes = resourceDir(baseDir).getAbsolutePath.split("/").toList.size

  testWithTimeout("Compiling testcases", 10.minutes) {
    val all = (filesIn(baseDir+"repair/") ++
               filesIn(baseDir+"runtime/") ++
               filesIn(baseDir+"synthesis/") ++
               filesIn(baseDir+"verification/") ++
               filesIn(baseDir+"web/")).sortBy(_.getAbsolutePath)

    info("Compiling "+all.size+" testcases...")

    all.par.foreach { f =>
      testFrontend(f, slashes)
    }
  }
}
