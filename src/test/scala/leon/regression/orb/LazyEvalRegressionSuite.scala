/* Copyright 2009-2016 EPFL, Lausanne */

package leon.regression.orb
import leon.test._

import leon._
import invariant.engine._
import laziness._
import verification._

import java.io.File

class LazyEvalRegressionSuite extends LeonRegressionSuite {
  private def forEachFileIn(path: String)(block: File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"))
    for (f <- fs) {
      block(f)
    }
  }

  private def testLazyVerification(f: File, ctx: LeonContext) {
    val beginPipe = leon.frontends.scalac.ExtractionPhase andThen
      new leon.utils.PreprocessingPhase
    val (ctx2, program) = beginPipe.run(ctx, f.getAbsolutePath :: Nil)
    val processPipe = LazinessEliminationPhase
    val (ctx3, report) = processPipe.run(ctx2, program)
    report.stateVerification match {
      case None => fail(s"No state verification report found!")
      case Some(rep) =>
        val fails = rep.vrs.collect{ case (vc, vr) if !vr.isValid => vc }
        if (!fails.isEmpty)
          fail(s"State verification failed for functions ${fails.map(_.fd).mkString("\n")}")
    }
    report.resourceVeri match {
      case None => fail(s"No resource verification report found!")
      case Some(rep: InferenceReport) =>
        val fails = rep.conditions.filterNot(_.prettyInv.isDefined)
        if (!fails.isEmpty)
          fail(s"Inference failed for functions ${fails.map(_.fd).mkString("\n")}")
      case Some(rep: VerificationReport) =>
        val fails = rep.vrs.collect{ case (vc, vr) if !vr.isValid => vc }
        if (!fails.isEmpty)
          fail(s"Resource verification failed for functions ${fails.map(_.fd).mkString("\n")}")
    }
  }

  forEachFileIn("regression/orb/lazy/withconst") { f =>
    test("Lazy evaluation w/o Orb: " + f.getName) {
      testLazyVerification(f, createLeonContext("--lazy", "--silent", "--timeout=30"))
    }
  }

  forEachFileIn("regression/orb/lazy/withorb") { f =>
    test("Lazy evaluation with Orb: " + f.getName) {
      testLazyVerification(f, createLeonContext("--lazy", "--useOrb", "--silent", "--vcTimeout=15", "--timeout=30"))
    }
  }
}
