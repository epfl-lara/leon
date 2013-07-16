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

import lesynth.refinement._
import lesynth.examples._
import lesynth.evaluation.CodeGenEvaluationStrategy
import lesynth.ranking.Candidate
import insynth.reconstruction.Output

import insynth.util._
import lesynth.util._

class EnumerationFastTest extends FunSuite {

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
	    val inSynth = new InSynthTemp(loader, true)
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
  
  test("Enumeration in Address example") {
        
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      expect(1) { problem.xs.size }
      val resultVariable = problem.xs.head
      val hole = Hole(resultVariable.getType)

	    val loader = new LeonLoader(program, hole, problem.as, false)
	    val inSynth = new InSynthTemp(loader, true)
	    // save all declarations seen
	    val allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
	    
		  val nilAbstractClassDef = program.definedClasses.find(_.id.name == "Nil").
		  	get.asInstanceOf[CaseClassDef]
	    val listVal = funDef.args.head.toVariable
      
      val variableRefiner = 
  			new VariableRefiner(loader.directSubclassesMap,
  					loader.variableDeclarations, loader.classMap)
      
	    val (refined, newDeclarations) = 
	      variableRefiner.checkRefinements(
          CaseClassInstanceOf(nilAbstractClassDef, listVal), BooleanLiteral(true), allDeclarations)
      assert(refined)
      assert(allDeclarations.size + 2 == newDeclarations.size)
      
      for (decl <- newDeclarations)
        println(decl.getSimpleName)
	    
	    val builder = new InitialEnvironmentBuilder(newDeclarations)
            
//	    val solver = inSynth.solver
//	    solver.getProofTree(builder)
//	    val solution = solver.getProofTree
//	    
//	    import ProofTreeOperations._
//	    assert(ProofTreeOperations.checkInhabitants(solution,
//        StringNode("AddressBook", Set(
//            //StringNode("[Cons=>List]", Set(StringNode("Cons"))),
//            StringNode("makeAddressBook", Set(StringNode("tail")))
//          ))
//        ))
	    
	    val outputs = inSynth.getExpressions(builder)
	    
      for (output <- outputs.take(20000))
        printf("%20s %5f\n", output.getSnippet.toString, output.getWeight)
	    
//	    val proofTree = inSynth.solver.getProofTree(builder)
//	    val os = new java.io.PrintWriter(new java.io.FileOutputStream("proofTree.xml"))
//	    insynth.util.format.TreePrinter.printAnswerAsXML(os, proofTree, 6)
    }
    
  }
  
  ignore("Enumeration in Address (mergeAddressBooks) example") {
        
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "AddressesMergeAddressBooks.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      expect(1) { problem.xs.size }
      val resultVariable = problem.xs.head
      val hole = Hole(resultVariable.getType)

	    val loader = new LeonLoader(program, hole, problem.as, false)
	    val inSynth = new InSynthTemp(loader, true)
	    // save all declarations seen
	    val allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
	    
//		  val nilAbstractClassDef = program.definedClasses.find(_.id.name == "Nil").
//		  	get.asInstanceOf[CaseClassDef]
//	    val listVal = funDef.args.head.toVariable
//      
//      val variableRefiner = 
//  			new VariableRefiner(loader.directSubclassesMap,
//  					loader.variableDeclarations, loader.classMap)
//      
//	    val (refined, newDeclarations) = 
//	      variableRefiner.checkRefinements(
//          CaseClassInstanceOf(nilAbstractClassDef, listVal), BooleanLiteral(true), allDeclarations)
//      assert(refined)
//      assert(allDeclarations.size + 2 == newDeclarations.size)
//      
//      for (decl <- newDeclarations)
//        println(decl.getSimpleName)
//	    
//	    val builder = new InitialEnvironmentBuilder(newDeclarations)
	    //assert(inSynth.getCurrentBuilder.getAllDeclarations.size > 13, { throw new RuntimeException; "aaa" })
//	    assert(false)
	    
	    val outputs = inSynth.getExpressions//(builder)
	    
//	    val proofTree = inSynth.solver.getProofTree(builder)
//	    val os = new java.io.PrintWriter(new java.io.FileOutputStream("proofTree.xml"))
//	    insynth.util.format.TreePrinter.printAnswerAsXML(os, proofTree, 6)
	          
      for (output <- outputs.take(20000))
        printf("%20s %5f\n", output.getSnippet.toString, output.getWeight)
    }
    
  }

}