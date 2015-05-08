/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.testcases

import leon._
import test.LeonTestSuite
import java.io.File

class TestCasesCompile extends LeonTestSuite {
  // Hard-code output directory, for Eclipse purposes

  val pipeline = frontends.scalac.ExtractionPhase andThen utils.PreprocessingPhase

  def testFrontend(f: File, strip: Int) = {
    val name = f.getAbsolutePath.split("/").toList.drop(strip).mkString("/")

    test("Compiling testcase " + name) {
      val ctx = createLeonContext()
      try {
        pipeline.run(ctx)(List(f.getAbsolutePath))
      } catch {
        case _: LeonFatalError =>
          fail("Failed to compile.")
      }
    }
  }

  private def forEachFileIn(path : String)(block : File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"), recursive=true)

    for(f <- fs.toSeq.sortBy(_.getAbsolutePath)) {
      block(f)
    }
  }

  val baseDir = "regression/testcases/"

  val slashes = resourceDir(baseDir).getAbsolutePath.split("/").toList.size

  forEachFileIn(baseDir+"repair/") { f =>
    testFrontend(f, slashes)
  }
  forEachFileIn(baseDir+"runtime/") { f =>
    testFrontend(f, slashes)
  }
  forEachFileIn(baseDir+"synthesis/") { f =>
    testFrontend(f, slashes)
  }
  forEachFileIn(baseDir+"verification/") { f =>
    testFrontend(f, slashes)
  }
  forEachFileIn(baseDir+"web/") { f =>
    testFrontend(f, slashes)
  }
}
