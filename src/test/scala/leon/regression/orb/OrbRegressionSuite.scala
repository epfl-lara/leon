/* Copyright 2009-2016 EPFL, Lausanne */

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

  private def testInference(f: File, bound: Option[Int] = None) {
    val ctx = createLeonContext("--inferInv", "--vcTimeout=3", "--solvers=smt-z3", "--silent", "--timeout=120")
    val beginPipe = leon.frontends.scalac.ExtractionPhase andThen
      new leon.utils.PreprocessingPhase
    val (ctx2, program) = beginPipe.run(ctx, f.getAbsolutePath :: Nil)
    val processPipe = InferInvariantsPhase
    val (ctx3, report) = processPipe.run(ctx2, program)
    if (report.conditions.isEmpty)
      fail(s"Nothing was solved")
    else {
      val fails = report.conditions.filterNot(_.prettyInv.isDefined)
      if (!fails.isEmpty)
        fail(s"Inference failed for functions ${fails.map(_.fd).mkString("\n")}")
    }
  }

  forEachFileIn("regression/orb/timing") { f =>
    test("Timing: " + f.getName) {
      testInference(f)
    }
  }

  forEachFileIn("regression/orb/stack/") { f =>
    test("Stack: " + f.getName) {
      testInference(f)
    }
  }

  forEachFileIn("regression/orb//depth") { f =>
    test("Depth: " + f.getName) {
      testInference(f)
    }
  }

  forEachFileIn("regression/orb/numerical") { f =>
    test("Numerical: " + f.getName) {
      testInference(f)
    }
  }

  forEachFileIn("regression/orb/combined/") { f =>
    test("Multiple Instrumentations: " + f.getName) {
      testInference(f)
    }
  }
}
