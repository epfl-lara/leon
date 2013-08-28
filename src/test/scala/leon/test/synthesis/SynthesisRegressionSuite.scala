/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package test
package synthesis

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
    val ctx = testContext.copy(settings = Settings(
        synthesis = true,
        xlang     = false,
        verify    = false
      ))

    val opts = SynthesisOptions(searchBound = Some(bound))

    val pipeline = plugin.ExtractionPhase andThen leon.utils.SubtypingPhase

    val program = pipeline.run(ctx)(f.getAbsolutePath :: Nil)

    var chooses = ChooseInfo.extractFromProgram(ctx, program, opts)

    for (ci <- chooses) {
      test(cat+": "+f.getName()+" - "+ci.fd.id.name) {
        val (sol, isComplete) = ci.synthesizer.synthesize()
        if (!isComplete) {
          fail("Solution was not found. (Search bound: "+bound+")")
        }
      }
    }
  }

  forEachFileIn("regression/synthesis/Church/") { f =>
    testSynthesis("Church", f, 200)
  }

  forEachFileIn("regression/synthesis/List/") { f =>
    testSynthesis("List", f, 200)
  }

  //forEachFileIn("regression/synthesis/SortedList/") { f =>
  //  testSynthesis("SortedList", f, 400)
  //}

  //forEachFileIn("regression/synthesis/StrictSortedList/") { f =>
  //  testSynthesis("StrictSortedList", f, 400)
  //}
}
