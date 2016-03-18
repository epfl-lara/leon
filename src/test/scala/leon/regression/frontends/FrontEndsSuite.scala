/* Copyright 2009-2016 EPFL, Lausanne */

package leon.regression.frontends

import leon._
import leon.test._
import java.io.File

class FrontEndsSuite extends LeonRegressionSuite {

  def testFrontend(f: File, forError: Boolean) = {
    val pipeline =
      frontends.scalac.ExtractionPhase     andThen
      new utils.PreprocessingPhase  andThen
      NoopPhase()

    test ("Testing " + f.getName) {
      val ctx = createLeonContext()
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

  val baseDir = "regression/frontends/"

  forEachFileIn(baseDir+"passing/") { f => 
    testFrontend(f, false)
  }
  forEachFileIn(baseDir+"error/simple/") { f =>
    testFrontend(f, true)
  }
  forEachFileIn(baseDir+"error/xlang/") { f =>
    testFrontend(f, true)
  }

}
