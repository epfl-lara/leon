package insynth

import insynth.leon._
import insynth.leon.loader._
import insynth.engine._

import insynth.reconstruction._
import insynth.reconstruction.{ stream => lambda }
import insynth.reconstruction.stream.{ OrderedStreamFactory }
import insynth.reconstruction.codegen._
import insynth.reconstruction.Output

import _root_.leon.purescala.Definitions._
import _root_.leon.purescala.Common._
import _root_.leon.purescala.TypeTrees._
import _root_.leon.purescala.Trees.{ Variable => LeonVariable, _ }

//import lesynth.refinement._
//import lesynth.examples._
//import lesynth.evaluation.CodeGenEvaluationStrategy
//import lesynth.ranking.Candidate

import org.junit.{ Test, Ignore }
import org.junit.Assert._
import org.scalatest.junit.JUnitSuite

import insynth.util.format._
import insynth.util._

import _root_.util._

import insynth.testutil.{ CommonProofTrees, CommonDeclarations, CommonLambda }

// TODO test abstractions (vals)
class InSynthTest extends JUnitSuite {

  import CommonDeclarations._
  import CommonProofTrees._
  import CommonLambda._
  import DeclarationFactory._
  
  import Scaffold._
  
	import ProofTreeOperations.StringNode

	val insynthTestDir = "testcases/condabd/test/insynth/" 
    
  val transformer = Streamer.apply _
  val codegen = (new CodeGenerator).apply _
  
  val maxElToOutput = 20
  
  import lambda.Node._
  
  def assertWeight(lambdaNode: lambda.Node, weight: Float) =
    assertEquals(size(lambdaNode), weight, 0f)
    
  def assertWeight(expected: Int, weight: Float) =
    assertEquals(expected.toFloat, weight, 0f)	
    
  def assertWeight(pair: (lambda.Node, Float)) =
    assertEquals("Node " + pair._1, size(pair._1), pair._2, 0f)	    
    
  def assertTake(stream: Stream[(lambda.Node, Float)], num: Int) = {
    val result = stream take num
    def message(pos: Int) = "Part of the resulting stream: " + result.slice(pos - 10, pos + 10).mkString("\n")
    
    for (ind <- 0 until result.size)
      assertWeight(result(ind))
    for (ind <- 0 until result.size - 1)
      assertTrue("Weights are not in non-decreasing order.\n" + "At position " + ind + "\n" + message(ind), stream(ind)._2 <= stream(ind + 1)._2)
    result
  }

  def assertNoDuplicity(extractorResults: Stream[(lambda.Node, Float)]) = {    
    // note that duplicates may exist in generated code (e.g. because coercions), but should not before that
    val duplicityMap = (Map[lambda.Node, Set[(lambda.Node, Float)]]() /: extractorResults) {
      (resMap, pair) =>
        val snippet = pair._1
        resMap + (snippet -> (resMap.getOrElse(snippet, Set.empty) + pair))
    }
          
    lazy val duplicityMessage = 
      for ( (key, value) <- duplicityMap.filter(_._2.size > 1).take(1)) yield
        ("Key: " + key) + ("\nValues: " + value.mkString("\n"))        
      
    assertTrue(
      "There are some duplications in generated code:\n" + duplicityMessage,
      duplicityMap.filter(_._2.size > 1).isEmpty
    )    
  }
  
  def interactivePause = {    
    System.out.println("Press Any Key To Continue...");
    new java.util.Scanner(System.in).nextLine();
  }
      
  @Test
  def testAddressesProofTree {  
  	
    for ((sctx, funDef, problem) <- forFile(insynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val inSynth = new InSynth(loader, resultVariable.getType, true)
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree
	    
	    assertTrue(
		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
        ProofTreeOperations.checkInhabitants(solution,
        StringNode("AddressBook", Set(
            StringNode("[Cons=>List]", Set(StringNode("Cons")))
            ,
            StringNode("pers", Set(StringNode("makeAddressBook")))
          ))
      ))
	    assertTrue(
		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
        ProofTreeOperations.checkInhabitants(solution,
        StringNode("addToPers", Set(
          StringNode("makeAddressBook", Set())
          , 
          StringNode("Address", Set( ))
        ))
      ))
	    assertTrue(
		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
        ProofTreeOperations.checkInhabitants(solution,
        StringNode("addToBusiness", Set(
          StringNode("makeAddressBook", Set())
          , 
          StringNode("Address", Set( ))
        ))
      ))
    }
  }
      
  @Test
  def testAddressesExpressionsTypeAddress {  
      	
    for ((sctx, funDef, problem) <- forFile(insynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val inSynth = new InSynth(loader, resultVariable.getType, true)
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree

      val extractorResults = assertTake(transformer(solution.getNodes.head, true), 1000)
      assertNoDuplicity(extractorResults)
	          
      val extractedSnipptes = extractorResults map { pair => codegen(pair._1) }
      
      val message = "Extracted: " + extractedSnipptes.size + "\n" +
        (for (output <- extractedSnipptes)
        	yield "%20s" format output).mkString("\n")
        	
    	val expectedSnipptes = List(
  	    "AddressBook(Nil, l)",
  	    "makeAddressBook(l)"
	    )
      
	    for (snippet <- expectedSnipptes)
	    	assertTrue(snippet + " not found in extracted. results:\n" + message,
    			extractedSnipptes.exists(_.toString == snippet.toString)
  			)

			assertTrue(
		    extractedSnipptes.exists(_.toString contains "addToPers")
	    )
			assertTrue(
		    extractedSnipptes.exists(_.toString contains "addToBusiness")
	    )
      
    }
  }
  
  @Ignore("See this weight bug in InSynth")
  @Test
  def testAddressesExpressionsTypeBoolean {  
      	
    for ((sctx, funDef, problem) <- forFile(insynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val inSynth = new InSynth(loader, BooleanType, true)
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree

      val extractorResults = assertTake(transformer(solution.getNodes.head, true), 1000)
      assertNoDuplicity(extractorResults)
      
      val extractedSnipptes = extractorResults map { pair => codegen(pair._1) }
      
      val message = "Extracted: " + extractedSnipptes.size + "\n" +
        (for (output <- extractedSnipptes)
        	yield "%20s" format output).mkString("\n")
        	
    	val expectedSnipptes = List(
  	    "allPrivate(AddressBook(Nil, l))",
  	    "allBusiness(makeAddressBook(l))",
  	    "allBusiness(makeAddressBook(l)) && allPrivate(AddressBook(Nil, l))"
	    )
      
	    for (snippet <- expectedSnipptes)
	    	assertTrue(snippet + " not found in extracted. results:\n" + message,
    			extractedSnipptes.exists(_.toString == snippet.toString)
  			)
    }
  }

  @Test
  def testAddressesExpressionsTypeAddressWithAddition {  
      	
    for ((sctx, funDef, problem) <- forFile(insynthTestDir + "AddressesWithAddition.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      // note problem.as does not contain function arguments, thus we use funDef.args
      //val varsInScope = problem.as

	    val loader = new LeonLoader(program, arguments.toList, false)
	    val inSynth = new InSynth(loader.load, resultVariable.getType, true)
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree
	          
      val extractedSnipptes = inSynth.getExpressions.map(_.getSnippet) take 1000
      
      val message = "Extracted: " + extractedSnipptes.size + "\n" +
        (for (output <- extractedSnipptes)
        	yield "%20s" format output).mkString("\n")
        	
    	val expectedSnipptes = List(
  	    "AddressBook(Nil, l)",
  	    "makeAddressBook(l, x, y)",
  	    "addToPers(AddressBook(l, l), Address(x, x, y))",
  	    "addToBusiness(AddressBook(l, l), Address(x, x, y))"
	    )
      
	    for (snippet <- expectedSnipptes)
	    	assertTrue(snippet + " not found in extracted. results:\n" + message,
    			extractedSnipptes.exists(_.toString == snippet.toString)
  			)
      
    }
  }

  @Test
  def testDeclarations {  
      	
    for ((sctx, funDef, problem) <- forFile(insynthTestDir + "AddressesWithAddition.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      // note problem.as does not contain function arguments, thus we use funDef.args
      //val varsInScope = problem.as

	    val loader = new LeonLoader(program, arguments.toList, false)
	    val inSynth = new InSynth(loader.load, resultVariable.getType, true)
	          
      val allDeclarations = inSynth.getAllDeclarations.map(d => (d.getSimpleName, d.leonType.toString)).toSet

      val expectedDeclarations = Set(
        ("AddressBook", "(List, List) => AddressBook"),
        ("[Cons=>List]", "Cons => List"),
        ("pers", "AddressBook => List"),
        ("addToPers", "(AddressBook, Address) => AddressBook"),
        ("addToBusiness", "(AddressBook, Address) => AddressBook"),
        ("l", "List"),
        ("tail", "Cons => List"),
        ("a", "Cons => Address"),
        ("x", "Int"),
        ("y", "Boolean")
  		)
  		
		  assertTrue(
	      "Expected:\n" + expectedDeclarations.mkString("\n") + "\nFound:\n" + allDeclarations.mkString("\n"),
	      expectedDeclarations.subsetOf(allDeclarations)	      
      )
    }
  }

}