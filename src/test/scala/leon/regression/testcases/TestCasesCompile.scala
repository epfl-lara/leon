/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.testcases

import leon._
import leon.test._
import org.scalatest.time.SpanSugar._
import java.io.File
import org.scalatest.ParallelTestExecution

class TestCasesCompile extends LeonRegressionSuite {
  val pipeline = frontends.scalac.ExtractionPhase andThen new utils.PreprocessingPhase(desugarXLang = true)

  private def filesIn(path : String): Seq[File] = {
    val fs = filesInResourceDir(path, _.endsWith(".scala"), recursive=true)

    fs.toSeq
  }

  val baseDir = "regression/testcases/"

  val allTests = (filesIn(baseDir+"repair/") ++
                 filesIn(baseDir+"runtime/") ++
                 filesIn(baseDir+"synthesis/") ++
                 filesIn(baseDir+"verification/") ++
                 filesIn(baseDir+"web/")).sortBy(_.getAbsolutePath)

  allTests.foreach { f =>

    val path = f.getAbsolutePath

    val index = path.indexOf(baseDir)
    val name = path.drop(index)

    test("Compiling "+name) {

      val ctx = createLeonContext()

      try {
        pipeline.run(ctx, List(f.getAbsolutePath))
      } catch {
        case fe: LeonFatalError =>
          fail(ctx, s"Failed to compile $name", fe)
      }
    }
  }
}
