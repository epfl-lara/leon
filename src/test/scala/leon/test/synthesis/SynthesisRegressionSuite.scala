/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.synthesis
import leon.test._

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.solvers.Solver
import leon.synthesis._
import leon.synthesis.utils._

import java.io.File

class SynthesisRegressionSuite extends LeonTestSuite {
  private def forEachFileIn(path : String)(block : File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"))

    for(f <- fs) {
      block(f)
    }
  }

  private def testSynthesis(cat: String, f: File, bound: Int) {

    var chooses = List[ChooseInfo]()
    var program: Program = null 
    var ctx: LeonContext = null 
    var opts: SynthesisSettings = null

    test(cat+": "+f.getName()+" Compilation") {
      ctx = createLeonContext("--synthesis")

      opts = SynthesisSettings(searchBound = Some(bound), allSeeing = true)

      val pipeline = leon.frontends.scalac.ExtractionPhase andThen leon.utils.PreprocessingPhase

      program = pipeline.run(ctx)(f.getAbsolutePath :: Nil)

      chooses = ChooseInfo.extractFromProgram(program)
    }

    for (ci <- chooses) {
      test(cat+": "+f.getName()+" - "+ci.fd.id.name) {
        val synthesizer = new Synthesizer(ctx, program, ci, opts)
        val (search, sols) = synthesizer.synthesize()
        if (sols.isEmpty) {
          fail("Solution was not found. (Search bound: "+bound+")")
        }
      }
    }
  }

  forEachFileIn("regression/synthesis/Church/") { f =>
    testSynthesis("Church", f, 200)
  }

  forEachFileIn("regression/synthesis/Examples/") { f =>
    testSynthesis("IOExamples", f, 200)
  }

  forEachFileIn("regression/synthesis/List/") { f =>
    testSynthesis("List", f, 200)
  }

  forEachFileIn("regression/synthesis/Holes/") { f =>
    testSynthesis("Holes", f, 1000)
  }
}
