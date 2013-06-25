package lesynth

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers._

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import java.io.{ BufferedWriter, FileWriter, File }
import leon.evaluators.CodeGenEvaluator
import leon.purescala.TreeOps
import leon.purescala.Common._
import leon.codegen.CodeGenEvalParams
import leon.purescala.TypeTrees._
import leon.evaluators.EvaluationResults._

import insynth._
import insynth.leon._
import insynth.leon.loader._
import insynth.engine._

import lesynth.examples.InputExamples
import lesynth.evaluation.CodeGenEvaluationStrategy
import lesynth.ranking.Candidate
import insynth.reconstruction.Output
import lesynth.examples.Example

import lesynth.util._

class EnumerationTest extends FunSuite {

  import Scaffold._
  import TestConfig._
  
  val CANDIDATES_TO_ENUMERATE = 50 :: 100 :: 1000 :: 10000 :: Nil
  
  val files = List("InsertionSortInsert.scala", "ListConcat.scala", "MergeSortSort.scala",
		"RedBlackTreeInsert.scala") map { lesynthTestDir + _ }

  ignore("Candidate enumeration duplicates") {
        
    for (candidatesToEnumerate <- CANDIDATES_TO_ENUMERATE; 
      file <- files;
    	(sctx, funDef, problem) <- forFile(file)) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      expect(1) { problem.xs.size }
      val resultVariable = problem.xs.head
      val hole = Hole(resultVariable.getType)

	    val loader = new LeonLoader(program, hole, problem.as, false)
	    val inSynth = new InSynth(loader, true)
	    // save all declarations seen
	    val allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
	    
	    val builder = new InitialEnvironmentBuilder(allDeclarations)
	    
	    val outputs = inSynth.getExpressions(builder)
	          
      val taken = outputs.take(candidatesToEnumerate).map(_.getSnippet).toList
      val takenDistinct = taken.distinct
      val takenRepeated = taken.filter(snip => taken.count(_ == snip) > 1)
      
      assert(taken.size == takenDistinct.size, "First " + candidatesToEnumerate +
        " are not distinct." +
        "Repeated #" + takenRepeated.size
        	+ ": " + takenRepeated.map(snip => snip.toString +
      	    " repeats " + taken.count(_ == snip)).mkString("\n")
      )
      assert(takenRepeated.isEmpty)
    }
  }

}