/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.synthesis

import leon.test._

import leon._
import leon.purescala.Definitions._
import leon.synthesis._

import java.io.File

class SynthesisRegressionSuite extends LeonRegressionSuite {
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

    test(cat+": "+f.getName+" Compilation") {
      ctx = createLeonContext("--synthesis")

      opts = SynthesisSettings(searchBound = Some(bound))

      val pipeline = leon.frontends.scalac.ExtractionPhase andThen new leon.utils.PreprocessingPhase

      program = pipeline.run(ctx)(f.getAbsolutePath :: Nil)

      chooses = ChooseInfo.extractFromProgram(ctx, program)
    }

    for (ci <- chooses) {
      test(cat+": "+f.getName+" - "+ci.fd.id.name) {
        val synthesizer = new Synthesizer(ctx, program, ci, opts)
        try {
          val (_, sols) = synthesizer.synthesize()
          if (sols.isEmpty) {
            fail("Solution was not found. (Search bound: "+bound+")")
          }
        } finally {
          synthesizer.shutdown()
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

  forEachFileIn("regression/synthesis/Misc/") { f =>
    testSynthesis("Miscellaneous", f, 1000)
  }

  forEachFileIn("regression/synthesis/Holes/") { f =>
    testSynthesis("Holes", f, 1000)
  }
}
