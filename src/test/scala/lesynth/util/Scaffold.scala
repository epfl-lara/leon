package lesynth
package util

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers._

import java.io.{BufferedWriter, FileWriter, File}

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.solvers.Solver
import leon.synthesis._
import leon.synthesis.utils._

object Scaffold {

  def forProgram(content: String): Iterable[(SynthesisContext, FunDef, Problem)] = {

    val ctx = LeonContext(
      settings = Settings(
        synthesis = true,
        xlang     = false,
        verify    = false		
      ),
      files = List(),
      reporter = new SilentReporter
    )
//    Settings.showIDs = true

    val pipeline = leon.plugin.TemporaryInputPhase andThen leon.plugin.ExtractionPhase andThen SynthesisProblemExtractionPhase

    val (program, results) = try {
      pipeline.run(ctx)((content, Nil))
    } catch {
      case _ =>
        fail("Error while processing")
    }
    
    extractProblems(ctx, program, results)
  }

  def forFile(file: String): Iterable[(SynthesisContext, FunDef, Problem)] = {
    val programFile = new File(file)
    
    val ctx = LeonContext(
      settings = Settings(
        synthesis = true,
        xlang     = false,
        verify    = false		
      ),
      files = List(programFile),
      reporter = new SilentReporter
    )

    val pipeline = leon.plugin.ExtractionPhase andThen SynthesisProblemExtractionPhase

    val (program, results) = try {
      pipeline.run(ctx)(file :: Nil)
    } catch {
      case _ =>
        fail("Error while processing " + file)
    }
    
    extractProblems(ctx, program, results)
  }
  
  private def extractProblems(ctx: LeonContext, program: Program, 
    problemMap: Map[leon.purescala.Definitions.FunDef,Seq[leon.synthesis.Problem]]) = {

    val opts = SynthesisOptions()
    
    val solver = new FairZ3Solver(ctx)
    solver.setProgram(program)

    val simpleSolver = new UninterpretedZ3Solver(ctx)
    simpleSolver.setProgram(program)

    for ((f, ps) <- problemMap; p <- ps) 
    	yield {
        val sctx = SynthesisContext(ctx,
                                    opts,
                                    Some(f),
                                    program,
                                    solver,
                                    simpleSolver,
                                    new SilentReporter,
                                    new java.util.concurrent.atomic.AtomicBoolean)

        (sctx, f, p)
    	}
  }
  
}