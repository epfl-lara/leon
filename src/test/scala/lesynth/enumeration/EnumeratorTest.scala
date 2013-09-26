package lesynth

import insynth.InSynth
import insynth.leon._
import insynth.leon.loader._
import insynth.engine._

import insynth.reconstruction._
import insynth.reconstruction.{ stream => lambda }
import insynth.reconstruction.stream.{ OrderedStreamFactory }
import insynth.reconstruction.codegen._
import insynth.reconstruction.Output

import _root_.leon._
import _root_.leon.purescala._
import _root_.leon.purescala.Definitions._
import _root_.leon.purescala.Common._
import _root_.leon.purescala.TypeTrees._
import _root_.leon.purescala.Trees.{ Variable => LeonVariable, _ }

import lesynth.refinement._
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

// this suggests we should refactor an enumerator class
class EnumeratorTest extends JUnitSuite {

  import CommonDeclarations._
  import CommonProofTrees._
  import CommonLambda._
  import DeclarationFactory._
  
  import Scaffold._
  
	import ProofTreeOperations.StringNode

	val lesynthTestDir = "testcases/condabd/test/lesynth/" 
    
  val transformer = Streamer.apply _
  val codegen = (new CodeGenerator).apply _
  
  def assertWeight(pair: Output) =
    assertEquals("Node " + pair.getSnippet + " does not have size " + pair.getWeight,
      TreeOps.formulaSize(pair.getSnippet).toFloat, pair.getWeight, 0f)
    
  def assertTake(insynth: InSynth, num: Int) = {
    val result = insynth.getExpressions take num

  // TODO this should be applied
//    def message(pos: Int) = "Part of the resulting stream: " + result.slice(pos - 10, pos + 10).mkString("\n")
//    
//    for (ind <- 0 until result.size)
//      assertWeight(result(ind))
//    for (ind <- 0 until result.size - 1)
//      assertTrue("Weights are not in non-decreasing order.\n" + "At position " + ind + "\n" + message(ind),
//        result(ind).getWeight <= result(ind + 1).getWeight)

    result.map(_.getSnippet)
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
  
  // note, refines first argument
  def refineListVariable(program: Program, funDef: FunDef,
    loader: LeonLoader, allDeclarations: List[LeonDeclaration], reporter: Reporter) = {	    
	  val nilAbstractClassDef = program.definedClasses.find(_.id.name == "Nil").
	  	get.asInstanceOf[CaseClassDef]
    val listVal = funDef.args.head.toVariable
    
    val variableRefiner = 
			new VariableRefiner(loader.directSubclassesMap,
					loader.variableDeclarations, loader.classMap, reporter)
    
    val (refined, newDeclarations) = 
      variableRefiner.checkRefinements(
        CaseClassInstanceOf(nilAbstractClassDef, listVal), BooleanLiteral(true), allDeclarations)
    assertTrue(refined)
    assert(allDeclarations.size + 2 == newDeclarations.size)
    
    val declsMessage = "newDeclarations do not contain needed declaration\nnewDeclarations: " +
      newDeclarations.map(decl => decl.getSimpleName + ":" + decl.getType).mkString("\n")
    assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "tail"))
    assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "a"))    

    newDeclarations
  }
 
  @Test
  def testAddressesWithRefinementProofTree {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val inSynth = new InSynth(loader, resultVariable.getType, true)
	    val allDeclarations = inSynth.getAllDeclarations
      
	    val newDeclarations = refineListVariable(program, funDef, loader, allDeclarations, sctx.reporter)

	    val builder = new InitialEnvironmentBuilder(newDeclarations)
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree(builder)
	          
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
    }
  }
      
  @Test
  def testAddressesWithRefinementSnippets {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)
      val reporter = sctx.reporter

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val newDeclarations = refineListVariable(program, funDef, loader, loader.load, reporter)	    
	    val inSynth = new InSynth(newDeclarations, resultVariable.getType, true)

      val extractedSnipptes = assertTake(inSynth, 1000)

      val message = "Extracted: " + extractedSnipptes.size + "\n" +
        (for (output <- extractedSnipptes)
        	yield "%20s" format output).mkString("\n")
        	
    	val expectedSnipptes = List(
  	    "AddressBook(Nil, l)",
  	    "makeAddressBook(l)",
  	    "addToPers(AddressBook(l, l), l.a)",
  	    "addToBusiness(makeAddressBook(l), l.a)"
	    )
      
	    for (snippet <- expectedSnipptes)
	    	assertTrue(snippet + " not found in extracted. results:\n" + message,
    			extractedSnipptes.exists(_.toString == snippet.toString)
  			)
    }
  } 
  
  @Test
  def testAddressesMergeWithRefinementSnippets {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "AddressesMergeAddressBooks.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)
      val reporter = sctx.reporter

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val inSynth = new InSynth(loader.load, resultVariable.getType, true)

      val extractedSnipptes = assertTake(inSynth, 15000)

      val message = "Extracted: " + extractedSnipptes.size + "\n" +
        (for (output <- extractedSnipptes)
        	yield "%20s" format output).mkString("\n")
        	
    	val expectedSnipptes = List(
  	    "AddressBook(ab1.pers, ab2.business)",
  	    "makeAddressBook(ab1.pers)",
  	    "AddressBook(merge(ab1.business, ab2.business), merge(ab2.pers, ab1.pers))"
	    )
      
	    for (snippet <- expectedSnipptes)
	    	assertTrue(snippet + " not found in extracted. results:\n" + message,
    			extractedSnipptes.exists(_.toString == snippet.toString)
  			)
    }
  } 
  
  @Test
  def testListConcatWithRefinementSnippets {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "ListConcat.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)
      val reporter = sctx.reporter

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val newDeclarations = refineListVariable(program, funDef, loader, loader.load, reporter)	
            
      val declsMessage = "newDeclarations do not contain needed declaration\nnewDeclarations: " +
        newDeclarations.map(decl => decl.getSimpleName + ":" + decl.getType).mkString("\n")
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l1.tail"))
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l1.head"))    

	    val inSynth = new InSynth(newDeclarations, resultVariable.getType, true)

      val extractedSnipptes = assertTake(inSynth, 1000)

      val message = "Extracted: " + extractedSnipptes.size + "\n" +
        (for (output <- extractedSnipptes)
        	yield "%20s" format output).mkString("\n")
        	
    	val expectedSnipptes = List(
  	    "concat(Nil(), l1)",
  	    "Cons(l1.head, Nil())",
  	    "Cons(l1.head, concat(l1.tail, l2))"
	    )
      
	    for (snippet <- expectedSnipptes)
	    	assertTrue(snippet + " not found in extracted. results:\n" + message,
    			extractedSnipptes.exists(_.toString == snippet.toString)
  			)
      
    }
  } 
  
  @Test
  def testAddressesWithRefinementBooleanSnippets {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)
      val reporter = sctx.reporter

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val newDeclarations = refineListVariable(program, funDef, loader, loader.load, reporter)	
            
      val declsMessage = "newDeclarations do not contain needed declaration\nnewDeclarations: " +
        newDeclarations.map(decl => decl.getSimpleName + ":" + decl.getType).mkString("\n")
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.a"))
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName contains "l.tail")) 
      assertTrue(declsMessage, newDeclarations.exists(_.getSimpleName == "l"))     

	    val inSynth = new InSynth(newDeclarations, BooleanType, true)

      val extractedSnipptes = assertTake(inSynth, 5000)

      val message = "Extracted: " + extractedSnipptes.size + "\n" +
        (for (output <- extractedSnipptes)
        	yield "%20s" format output).mkString("\n")
        	
    	val expectedSnipptes = List(
  	    // FIXME!
  	    // this one is harder to get since it has coercion for l
//  	    "allBusiness(AddressBook(Nil, l).pers)",
//  	    "allBusiness(AddressBook(Nil, l.tail).pers)",
  	    "allBusiness(makeAddressBook(l).business)",
  	    "allBusiness(l.tail)",
  	    "allPrivate(addToBusiness(makeAddressBook(l), l.a).pers)"
	    )
      
	    for (snippet <- expectedSnipptes)
	    	assertTrue(snippet + " not found in extracted. results:\n" + message,
    			extractedSnipptes.exists(_.toString == snippet.toString)
  			)
    }
  } 
 
  @Test
  def testAddressesWithRefinementBooleanProofTree {  
  	
    for ((sctx, funDef, problem) <- forFile(lesynthTestDir + "Addresses.scala")) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val inSynth = new InSynth(loader, BooleanType, true)
	    val allDeclarations = inSynth.getAllDeclarations
      
	    val newDeclarations = refineListVariable(program, funDef, loader, allDeclarations, sctx.reporter)

	    val builder = new InitialEnvironmentBuilder(newDeclarations)
	    val solver = inSynth.solver	    
	    val solution = solver.getProofTree(builder)
	          
	    assertTrue(
		    ProofTreeOperations.breadthFirstSearchPrint(solution.getNodes.head),
        ProofTreeOperations.checkInhabitants(solution,
        StringNode("allBusiness", Set(
	        StringNode("pers", Set(
		        StringNode("AddressBook", Set(
	            StringNode("[Nil=>List]", Set(StringNode("Nil", Set())))
	            ,
	            StringNode("[Cons=>List]", Set(StringNode("l", Set())))
	            ,
	            StringNode("l.tail", Set())
	          ))
          ))
        ))
      ))
	    
    }
  }
  
  val CANDIDATES_TO_ENUMERATE = 50 :: 100 :: 1000 :: 10000 :: Nil
  
  val files = List("InsertionSortInsert.scala", "ListConcat.scala", "MergeSortSort.scala",
		"RedBlackTreeInsert.scala") map { lesynthTestDir + _ }

  @Ignore
  @Test
  def candidateEnumerationDuplicatesTest {
        
    for (candidatesToEnumerate <- CANDIDATES_TO_ENUMERATE; 
      file <- files;
    	(sctx, funDef, problem) <- forFile(file)) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)
      val reporter = sctx.reporter

      assertEquals(1, problem.xs.size)
      val resultVariable = problem.xs.head
      val varsInScope = problem.as

	    val loader = new LeonLoader(program, varsInScope, false)
	    val inSynth = new InSynth(loader.load, resultVariable.getType, true)
	    
	    val outputs = inSynth.getExpressions
	          
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