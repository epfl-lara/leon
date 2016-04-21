/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.xlang

import leon._
import leon.test._
import purescala.Definitions.Program
import java.io.File

class XLangDesugaringSuite extends LeonRegressionSuite {
  // Hard-code output directory, for Eclipse purposes

  val pipeline = frontends.scalac.ExtractionPhase andThen new utils.PreprocessingPhase

  def testFrontend(f: File, forError: Boolean) = {
    test ("Testing " + f.getName) {
      val ctx = createLeonContext("--timeout=40")
      if (forError) {
        intercept[LeonFatalError]{
          pipeline.run(ctx, List(f.getAbsolutePath))
        }
      } else {
        pipeline.run(ctx, List(f.getAbsolutePath))
      }
    }

  }

  private def forEachFileIn(path : String)(block : File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"))

    for(f <- fs) {
      block(f)
    } 
  }

  val baseDir = "regression/xlang/"

  forEachFileIn(baseDir+"passing/") { f => 
    testFrontend(f, false)
  }
  forEachFileIn(baseDir+"error/") { f =>
    testFrontend(f, true)
  }
   
}
