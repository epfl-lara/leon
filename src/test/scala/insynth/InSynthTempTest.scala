package insynth

import insynth.leon._
import insynth.leon.loader._
import insynth.engine._

import insynth.reconstruction.{ intermediate => int }
import insynth.reconstruction.{ stream => lambda }
import insynth.reconstruction.shortcut._
import insynth.reconstruction.stream.{ OrderedStreamFactory }
import insynth.reconstruction.codegen._
import insynth.reconstruction.Output

import _root_.leon.purescala.Definitions._
import _root_.leon.purescala.Common._
import _root_.leon.purescala.TypeTrees._
import _root_.leon.purescala.Trees.{ Variable => LeonVariable, _ }

import lesynth.refinement._
import lesynth.examples._
import lesynth.evaluation.CodeGenEvaluationStrategy
import lesynth.ranking.Candidate

import org.junit.{ Test, Ignore }
import org.junit.Assert._

import insynth.util.format._
import insynth.util._
import lesynth.util._

import insynth.testutil.{ CommonProofTrees, CommonDeclarations, CommonLambda }

// TODO test abstractions (vals)
class InSynthTempTest {

  import CommonDeclarations._
  import CommonProofTrees._
  import CommonLambda._
  import DeclarationFactory._
  
  import Scaffold._
  import TestConfig._
  
	import ProofTreeOperations.StringNode
    
  val transformer = new Transformer2(new OrderedStreamFactory)
  val codegen = new CodeGenerator
  
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
    val message = "Part of the resulting stream: " + result.take(maxElToOutput).mkString("\n")
    
    for (ind <- 0 until result.size)
      assertWeight(result(ind))
    for (ind <- 0 until result.size - 1)
      assertTrue("Weight are not in non-decreasing order.\n" + "At position " + ind + "\n" + message, stream(ind)._2 <= stream(ind + 1)._2)
    result
  }
  
  def interactivePause = {    
    System.out.println("Press Any Key To Continue...");
    new java.util.Scanner(System.in).nextLine();
  }
      
  @Ignore
  def testAddresses: Unit = {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val hole = Hole(resultVariable.getType)

	    val loader = new LeonLoader(program, hole, problem.as, false)
	    val inSynth = new InSynthTemp(loader, true)
	    // save all declarations seen
	    val allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
	    
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
          StringNode("makeAddressBook", Set(
//        		StringNode("l.tail", Set())
          ))
          , 
          StringNode("Address", Set( ))
        ))
      ))
	    assertTrue(
		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
        ProofTreeOperations.checkInhabitants(solution,
        StringNode("addToBusiness", Set(
          StringNode("makeAddressBook", Set(
//        		StringNode("l.tail", Set())
          ))
          , 
          StringNode("Address", Set( ))
        ))
      ))
      
      val extractorResults = assertTake(transformer(solution.getNodes.head), 1000)
	          
//      val duplicityMap = (Map[Expr, Set[(lambda.Node, Float)]]() /: extractorResults) {
//        (resMap, pair) =>
//          val snippet = codegen(pair._1)
//          resMap + (snippet -> (resMap.getOrElse(snippet, Set.empty) + pair))
//      }
      
//      val resTemp = transformer(solution.getNodes.head).take(100)
//      
//      println(resTemp.head)
//      val it = resTemp.iterator.buffered
//      println(it.head)
//      println(it.hasNext)
//      println(it.head)
//      println(it.hasNext)
//      
//      for (output <- extractorResults) {
//      	print("%20s %5f" format (output._1, output._2))
//      	
//		    System.out.println("Press Any Key To Continue...");
//		    new java.util.Scanner(System.in).nextLine();
//      }
//      println("\nExtracted: " + extractorResults.size)
       	
      val message = 
        (for (output <- extractorResults)
        	yield "%20s %5f" format (output._1, output._2)).mkString("\n") + "\nExtracted: " + extractorResults.size
      assertTrue("addToPers not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToPers"))
      assertTrue("addToBusiness not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToBusiness"))
//      
//      println("Duplicity map size " + duplicityMap.size)
//      for ( (key, value) <- duplicityMap.filter(_._2.size > 1).take(1)) {
//        println("Key: " + key)
//        println("Values: " + value.mkString("\n"))        
//      }
    }
  }
 
  @Ignore
  def testAddressesWithRefinement: Unit = {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
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
      
      val declsMessage = "newDeclarations do not contain needed declaration\nnewDeclarations: " +
        newDeclarations.map(decl => decl.getSimpleName + ":" + decl.getType).mkString("\n")
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.tail"))
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.a"))
	    println(declsMessage)      
      
	    val builder = new InitialEnvironmentBuilder(newDeclarations)
      
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree(builder)
      
      val extractorResults = assertTake(transformer(solution.getNodes.head), 1000)
	          
//      val duplicityMap = (Map[Expr, Set[(lambda.Node, Float)]]() /: extractorResults) {
//        (resMap, pair) =>
//          val snippet = codegen(pair._1)
//          resMap + (snippet -> (resMap.getOrElse(snippet, Set.empty) + pair))
//      }
      
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
          StringNode("makeAddressBook", Set(
        		StringNode("l.tail", Set())
          ))
          , 
          StringNode("a", Set( ))
        ))
      ))
	    assertTrue(
		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
        ProofTreeOperations.checkInhabitants(solution,
        StringNode("addToBusiness", Set(
          StringNode("makeAddressBook", Set(
        		StringNode("l.tail", Set())
          ))
          , 
          StringNode("a", Set( ))
        ))
      ))
	    assertTrue(
		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
        ProofTreeOperations.checkInhabitants(solution,
        StringNode("addToBusiness", Set(
          StringNode("makeAddressBook", Set(
        		StringNode("l.tail", Set())
          ))
          , 
          StringNode("l.a", Set( ))
        ))
      ))
//      val resTemp = transformer(solution.getNodes.head).take(100)
//      
//      println(resTemp.head)
//      val it = resTemp.iterator.buffered
//      println(it.head)
//      println(it.hasNext)
//      println(it.head)
//      println(it.hasNext)
//      
//      for (output <- extractorResults) {
//      	print("%20s %5f" format (output._1, output._2))
//      	
//		    System.out.println("Press Any Key To Continue...");
//		    new java.util.Scanner(System.in).nextLine();
//      }
//      println("\nExtracted: " + resTemp.size)
//    	println("\nExtracted: " + extractorResults.size)
       	
      val message = 
        (for (output <- extractorResults)
        	yield "%20s %5f" format (output._1, output._2)).mkString("\n") + "\nExtracted: " + extractorResults.size
      assertTrue("addToPers not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToPers"))
      assertTrue("addToBusiness not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToBusiness"))
//      
//      println("Duplicity map size " + duplicityMap.size)
//      for ( (key, value) <- duplicityMap.filter(_._2.size > 1).take(1)) {
//        println("Key: " + key)
//        println("Values: " + value.mkString("\n"))        
//      }
    }
  } 
 
  @Ignore
  def testAddressesWithRefinementCodeGen: Unit = {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
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
      
      val declsMessage = "newDeclarations do not contain needed declaration\nnewDeclarations: " +
        newDeclarations.map(decl => decl.getSimpleName + ":" + decl.getType).mkString("\n")
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.tail"))
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.a"))
	    println(declsMessage)      
      
	    val builder = new InitialEnvironmentBuilder(newDeclarations)
      
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree(builder)
      
      val extractorResults = assertTake(transformer(solution.getNodes.head), 20000)
	          
      var ind = 1
      for ((output, snippet) <- extractorResults zip (extractorResults map { p => codegen(p._1) })) {
      	print("%20s %20s\n".format(snippet, output._1.toString))
      	ind +=1     	
      	
      	if ((ind % 1000) == 0) {
      	  interactivePause
      	}
      }
       	
      val message = 
        (for (output <- extractorResults)
        	yield "%20s %5f" format (output._1, output._2)).mkString("\n") + "\nExtracted: " + extractorResults.size
      assertTrue("addToPers not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToPers"))
      assertTrue("addToBusiness not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToBusiness"))
//      
//      println("Duplicity map size " + duplicityMap.size)
//      for ( (key, value) <- duplicityMap.filter(_._2.size > 1).take(1)) {
//        println("Key: " + key)
//        println("Values: " + value.mkString("\n"))        
//      }
    }
  } 
  
  @Ignore
  def testAddressesWithRefinementTime: Unit = {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
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
      
      val declsMessage = "newDeclarations do not contain needed declaration\nnewDeclarations: " +
        newDeclarations.map(decl => decl.getSimpleName + ":" + decl.getType).mkString("\n")
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.tail"))
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.a"))
      
	    val builder = new InitialEnvironmentBuilder(newDeclarations)
      
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree(builder)
      
	    val startTime = System.currentTimeMillis
      val extractorResults = assertTake(transformer(solution.getNodes.head), 5000)
      println("Time for extracting 5000 solutions: " + (System.currentTimeMillis - startTime))
	          
//      val duplicityMap = (Map[Expr, Set[(lambda.Node, Float)]]() /: extractorResults) {
//        (resMap, pair) =>
//          val snippet = codegen(pair._1)
//          resMap + (snippet -> (resMap.getOrElse(snippet, Set.empty) + pair))
//      }
      
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
          StringNode("makeAddressBook", Set(
        		StringNode("l.tail", Set())
          ))
          , 
          StringNode("a", Set( ))
        ))
      ))
	    assertTrue(
		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
        ProofTreeOperations.checkInhabitants(solution,
        StringNode("addToBusiness", Set(
          StringNode("makeAddressBook", Set(
        		StringNode("l.tail", Set())
          ))
          , 
          StringNode("a", Set( ))
        ))
      ))
	    assertTrue(
		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
        ProofTreeOperations.checkInhabitants(solution,
        StringNode("addToBusiness", Set(
          StringNode("makeAddressBook", Set(
        		StringNode("l.tail", Set())
          ))
          , 
          StringNode("l.a", Set( ))
        ))
      ))
//      val resTemp = transformer(solution.getNodes.head).take(100)
//      
//      println(resTemp.head)
//      val it = resTemp.iterator.buffered
//      println(it.head)
//      println(it.hasNext)
//      println(it.head)
//      println(it.hasNext)
//      
//      for (output <- extractorResults) {
//      	print("%20s %5f" format (output._1, output._2))
//      	
//		    System.out.println("Press Any Key To Continue...");
//		    new java.util.Scanner(System.in).nextLine();
//      }
//      println("\nExtracted: " + resTemp.size)
//    	println("\nExtracted: " + extractorResults.size)
       	
      val message = 
        (for (output <- extractorResults)
        	yield "%20s %5f" format (output._1, output._2)).mkString("\n") + "\nExtracted: " + extractorResults.size
      assertTrue("addToPers not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToPers"))
      assertTrue("addToBusiness not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToBusiness"))
//      
//      println("Duplicity map size " + duplicityMap.size)
//      for ( (key, value) <- duplicityMap.filter(_._2.size > 1).take(1)) {
//        println("Key: " + key)
//        println("Values: " + value.mkString("\n"))        
//      }
    }
  } 
 
  @Ignore
  def testListConcatWithRefinementCodeGen: Unit = {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthSynthesisDir + "List/ListConcat.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
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
      
      val declsMessage = "newDeclarations do not contain needed declaration\nnewDeclarations: " +
        newDeclarations.map(decl => decl.getSimpleName + ":" + decl.getType).mkString("\n")
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l1.tail"))
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l1.head"))
	    println(declsMessage)      
      
	    val builder = new InitialEnvironmentBuilder(newDeclarations)
      
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree(builder)
      
      val extractorResults = assertTake(transformer(solution.getNodes.head), 1000)
	          
      var ind = 1
      for ((output, snippet) <- extractorResults zip (extractorResults map { p => codegen(p._1) })) {
      	print("%20s %20s\n".format(snippet, output._1.toString))
      	ind +=1     	
      	
      	if ((ind % 1000) == 0) {
      	  interactivePause
      	}
      }
       	
//      val message = 
//        (for (output <- extractorResults)
//        	yield "%20s %5f" format (output._1, output._2)).mkString("\n") + "\nExtracted: " + extractorResults.size
//      assertTrue("addToPers not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToPers"))
//      assertTrue("addToBusiness not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToBusiness"))
//      
//      println("Duplicity map size " + duplicityMap.size)
//      for ( (key, value) <- duplicityMap.filter(_._2.size > 1).take(1)) {
//        println("Key: " + key)
//        println("Values: " + value.mkString("\n"))        
//      }
    }
  } 
  
  @Test
  def testAddressesWithRefinementBoolean: Unit = {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val hole = Hole(BooleanType)

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
      
      val declsMessage = "newDeclarations do not contain needed declaration\nnewDeclarations: " +
        newDeclarations.map(decl => decl.getSimpleName + ":" + decl.getType).mkString("\n")
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.tail"))
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.a"))
	    println(declsMessage)      
      
	    val builder = new InitialEnvironmentBuilder(newDeclarations)
      
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree(builder)
      
      val extractorResults = assertTake(transformer(solution.getNodes.head), 100)
	          
//      val duplicityMap = (Map[Expr, Set[(lambda.Node, Float)]]() /: extractorResults) {
//        (resMap, pair) =>
//          val snippet = codegen(pair._1)
//          resMap + (snippet -> (resMap.getOrElse(snippet, Set.empty) + pair))
//      }
      
//	    assertTrue(
//		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
//        ProofTreeOperations.checkInhabitants(solution,
//        StringNode("AddressBook", Set(
//            StringNode("[Cons=>List]", Set(StringNode("Cons")))
//            ,
//            StringNode("pers", Set(StringNode("makeAddressBook")))
//          ))
//      ))
//	    assertTrue(
//		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
//        ProofTreeOperations.checkInhabitants(solution,
//        StringNode("addToPers", Set(
//          StringNode("makeAddressBook", Set(
//        		StringNode("l.tail", Set())
//          ))
//          , 
//          StringNode("a", Set( ))
//        ))
//      ))
//	    assertTrue(
//		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
//        ProofTreeOperations.checkInhabitants(solution,
//        StringNode("addToBusiness", Set(
//          StringNode("makeAddressBook", Set(
//        		StringNode("l.tail", Set())
//          ))
//          , 
//          StringNode("a", Set( ))
//        ))
//      ))
//	    assertTrue(
//		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
//        ProofTreeOperations.checkInhabitants(solution,
//        StringNode("addToBusiness", Set(
//          StringNode("makeAddressBook", Set(
//        		StringNode("l.tail", Set())
//          ))
//          , 
//          StringNode("l.a", Set( ))
//        ))
//      ))
//      val resTemp = transformer(solution.getNodes.head).take(100)
//      
//      println(resTemp.head)
//      val it = resTemp.iterator.buffered
//      println(it.head)
//      println(it.hasNext)
//      println(it.head)
//      println(it.hasNext)
//      
      for (output <- extractorResults) {
      	print("%20s %5f" format (output._1, output._2))
      	
		    System.out.println("Press Any Key To Continue...");
		    new java.util.Scanner(System.in).nextLine();
      }
//      println("\nExtracted: " + resTemp.size)
//    	println("\nExtracted: " + extractorResults.size)
       	
//      val message = 
//        (for (output <- extractorResults)
//        	yield "%20s %5f" format (output._1, output._2)).mkString("\n") + "\nExtracted: " + extractorResults.size
//      assertTrue("addToPers not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToPers"))
//      assertTrue("addToBusiness not found in extracted. results:\n" + message, extractorResults.exists(_._1.toString contains "addToBusiness"))
//      
//      println("Duplicity map size " + duplicityMap.size)
//      for ( (key, value) <- duplicityMap.filter(_._2.size > 1).take(1)) {
//        println("Key: " + key)
//        println("Values: " + value.mkString("\n"))        
//      }
    }
  } 
 

}