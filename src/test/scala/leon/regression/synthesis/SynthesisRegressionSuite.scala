/* Copyright 2009-2016 EPFL, Lausanne */

package leon.regression.synthesis

import leon.test._

import leon._
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
    val ctx = createLeonContext("--synthesis", "--solvers=smt-z3")

    val pipeline = leon.frontends.scalac.ExtractionPhase andThen new leon.utils.PreprocessingPhase

    val (ctx2, program) = try {
      pipeline.run(ctx, f.getAbsolutePath :: Nil)
    } catch {
      case LeonFatalError(msg) =>
        test(s"$cat: ${f.getName}") {
          fail(s"Compilation failed: ${msg.getOrElse("")}")
        }
        return
    }

    val chooses = SourceInfo.extractFromProgram(ctx2, program)
    val settings = SynthesisSettings(searchBound = Some(bound))

    for (ci <- chooses) {
      test(s"$cat: ${f.getName} - ${ci.fd.id.name}") {
        val synthesizer = new Synthesizer(ctx, program, ci, settings)
        try {
          val (_, sols) = synthesizer.synthesize()
          if (sols.isEmpty) {
            fail(s"Solution was not found. (Search bound: $bound)")
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
