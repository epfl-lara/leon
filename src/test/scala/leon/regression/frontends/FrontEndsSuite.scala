/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.frontends

import leon._
import leon.test._
import purescala.Definitions.Program
import java.io.File

class FrontEndsSuite extends LeonRegressionSuite {
  // Hard-code output directory, for Eclipse purposes

  val pipeFront = frontends.scalac.ExtractionPhase andThen new utils.PreprocessingPhase

  def testFrontend(f: File, pipeBack: Pipeline[Program, Program], forError: Boolean) = {
    val pipeline = pipeFront andThen pipeBack
    test ("Testing " + f.getName) {
      val ctx = createLeonContext()
      if (forError) {
        intercept[LeonFatalError]{
          pipeline.run(ctx)(List(f.getAbsolutePath))
        }
      } else {
        pipeline.run(ctx)(List(f.getAbsolutePath))
      }
    }

  }

  private def forEachFileIn(path : String)(block : File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"))

    for(f <- fs) {
      block(f)
    } 
  }

  val pipeNormal = xlang.NoXLangFeaturesChecking andThen NoopPhase() // redundant NoopPhase to trigger throwing error between phases
  val pipeX = NoopPhase[Program]()
  val baseDir = "regression/frontends/"

  forEachFileIn(baseDir+"passing/") { f => 
    testFrontend(f, pipeNormal, false)
  }
  forEachFileIn(baseDir+"error/simple/") { f =>
    testFrontend(f, pipeNormal, true)
  }
  forEachFileIn(baseDir+"error/xlang/") { f =>
    testFrontend(f, pipeX, true)
  }
   
}
