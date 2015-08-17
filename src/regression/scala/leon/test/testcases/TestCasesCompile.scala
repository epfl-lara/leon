/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.testcases

import leon._
import org.scalatest.time.SpanSugar._
import test.LeonTestSuite
import java.io.File
import org.scalatest.ParallelTestExecution

class TestCasesCompile extends LeonTestSuite {
  val pipeline = frontends.scalac.ExtractionPhase andThen utils.PreprocessingPhase

  private def filesIn(path : String): Seq[File] = {
    val fs = filesInResourceDir(path, _.endsWith(".scala"), recursive=true)

    fs.toSeq
  }

  val baseDir = "regression/testcases/"

  val slashes = resourceDir(baseDir).getAbsolutePath.split("/").toList.size

  val allTests = (filesIn(baseDir+"repair/") ++
                 filesIn(baseDir+"runtime/") ++
                 filesIn(baseDir+"synthesis/") ++
                 filesIn(baseDir+"verification/") ++
                 filesIn(baseDir+"web/")).sortBy(_.getAbsolutePath)

  allTests.foreach { f =>
    val name = f.getAbsolutePath.split("/").toList.drop(slashes).mkString("/")

    test("Compiling "+name) {

      val ctx = createLeonContext()

      try {
        pipeline.run(ctx)(List(f.getAbsolutePath))
      } catch {
        case _: LeonFatalError =>
          fail(" Failed to compile "+name)
      }
    }
  }
}
