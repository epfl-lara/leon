/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.orb
import leon.test._

import leon._
import leon.purescala.Definitions._
import leon.invariant.engine._
import leon.transformations._

import java.io.File

class OrbRegressionSuite extends LeonRegressionSuite {
  private def forEachFileIn(path: String)(block: File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"))
    for (f <- fs) {
      block(f)
    }
  }

  private def testInference(f: File, bound: Int) {

    val ctx = createLeonContext("--inferInv", "--minbounds", "--timeout="+bound)
    val beginPipe = leon.frontends.scalac.ExtractionPhase andThen
      new leon.utils.PreprocessingPhase
    val program = beginPipe.run(ctx)(f.getAbsolutePath :: Nil)
    val processPipe = InstrumentationPhase andThen InferInvariantsPhase
    val report = processPipe.run(ctx)(program)
    val fails = report.conditions.filterNot(_.invariant.isDefined)
    if (!fails.isEmpty)
      fail(s"Inference failed for functions ${fails.map(_.fd).mkString("\n")}")
  }

  forEachFileIn("regression/orb/timing") { f =>
    test("Timing: " + f.getName) {
      testInference(f, 50)
    }
  }

  forEachFileIn("regression/orb/stack/") { f =>
    test("Stack: " + f.getName) {
      testInference(f, 50)
    }
  }

  forEachFileIn("regression/orb//depth") { f =>
    test("Depth: " + f.getName) {
      testInference(f, 50)
    }
  }

  forEachFileIn("regression/orb/numerical") { f =>
    test("Numerical: " + f.getName) {
      testInference(f, 50)
    }
  }

  forEachFileIn("regression/orb/combined/") { f =>
    test("Multiple Instrumentations: " + f.getName) {
      testInference(f, 50)
    }
  }
}
