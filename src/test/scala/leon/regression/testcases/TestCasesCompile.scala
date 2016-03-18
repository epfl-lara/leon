/* Copyright 2009-2016 EPFL, Lausanne */

package leon.regression.testcases

import leon._
import leon.test._
import java.io.File

abstract class TestCasesCompile(testDir: String) extends LeonRegressionSuite {

  val pipeline = frontends.scalac.ExtractionPhase andThen new utils.PreprocessingPhase

  private def filesIn(path : String): Seq[File] = {
    val fs = filesInResourceDir(path, _.endsWith(".scala"), recursive=true)

    fs.toSeq
  }

  val baseDir = "regression/testcases/"

  val allTests = filesIn(baseDir + testDir)

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

class TestcasesCompile1 extends TestCasesCompile("repair/")
class TestcasesCompile2 extends TestCasesCompile("runtime/")
class TestcasesCompile3 extends TestCasesCompile("synthesis/")
class TestcasesCompile4 extends TestCasesCompile("verification/")
class TestcasesCompile5 extends TestCasesCompile("web/")
