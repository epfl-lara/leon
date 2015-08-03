/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.testcases

import leon._
import org.scalatest.time.SpanSugar._
import test.LeonTestSuite
import java.io.File
import org.scalatest.ParallelTestExecution

class TestCasesCompile extends LeonTestSuite {
  val pipeline = frontends.scalac.ExtractionPhase andThen utils.PreprocessingPhase

  def testFrontend(f: File, strip: Int): Boolean = {
    val name = f.getAbsolutePath.split("/").toList.drop(strip).mkString("/")

    val ctx = createLeonContext()

    try {
      pipeline.run(ctx)(List(f.getAbsolutePath))
      info(name)
      true
    } catch {
      case _: LeonFatalError =>
        info(Console.YELLOW+" Failed to compile "+name)
        false
    }
  }

  private def filesIn(path : String): Seq[File] = {
    val fs = filesInResourceDir(path, _.endsWith(".scala"), recursive=true)

    fs.toSeq
  }

  val baseDir = "regression/testcases/"

  val slashes = resourceDir(baseDir).getAbsolutePath.split("/").toList.size

  testWithTimeout("Compiling testcases", 20.minutes) {
    val all = (filesIn(baseDir+"repair/") ++
               filesIn(baseDir+"runtime/") ++
               filesIn(baseDir+"synthesis/") ++
               filesIn(baseDir+"verification/") ++
               filesIn(baseDir+"web/")).sortBy(_.getAbsolutePath)

    info("Compiling "+all.size+" testcases...")

    var nFailed = new java.util.concurrent.atomic.AtomicInteger(0)
    all.foreach { f =>
      if (!testFrontend(f, slashes)) {
        nFailed.incrementAndGet()
      }
    }

    val nFailedInt = nFailed.get()
    if (nFailedInt > 0) {
      fail(s"$nFailedInt test(s) failed to compile")
    }
  }
}
