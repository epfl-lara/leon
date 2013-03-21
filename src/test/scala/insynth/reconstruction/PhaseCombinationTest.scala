package insynth.reconstruction

import org.junit.{ Test, Ignore }
import org.junit.Assert._

import insynth.reconstruction.intermediate.IntermediateTransformer
import insynth.reconstruction.stream.{ Extractor, UnorderedStreamFactory }
import insynth.reconstruction.codegen.CodeGenerator

import leon.purescala.Definitions.{ FunDef, VarDecl, Program, ObjectDef }
import leon.purescala.Common.{ FreshIdentifier }
import leon.purescala.TypeTrees._
import leon.purescala.Trees.{ Variable => LeonVariable, _ }

import insynth.testutil.{ CommonProofTrees, CommonDeclarations, CommonIntermediate, CommonLambda, CommonLeonExpressions }

class PhaseCombinationTest {

  import CommonDeclarations._
  import CommonProofTrees._
  import CommonIntermediate._
  import CommonLambda._
  import CommonLeonExpressions._
      
  @Test
  def treeBoolToInt {
    val (queryNode, query) = exampleBoolToInt
    
    val intermediateTree = IntermediateTransformer(queryNode)
        
    val codeGenerator = new CodeGenerator
    
    val extractor = new Extractor(new UnorderedStreamFactory)
    
    val extractorResults = extractor(intermediateTree) take 1
    
    assertEquals(1, extractorResults.size)
    
    val codeGenResult = codeGenerator(extractorResults.head._1)
    
    assertEquals(FunctionInvocation(functionBoolToIntFunDef, List(BooleanLiteral(false))), codeGenResult)    
  }
  
  @Test
  def treeIntToIntBoth {
    val queryNode = exampleIntToIntBoth
    
    val intermediateTree = IntermediateTransformer(queryNode)
    
    assertEquals(constructIntToIntIntermediateBoth, intermediateTree)
            
    val extractor = new Extractor(new UnorderedStreamFactory)
    
    val extractorResults = (extractor(intermediateTree) take (5 * 2 * 2)) map { _._1 }	    
    
    assertEquals(5 * 4, extractorResults.size)	    	  
    
    for (node <- constructIntAndBoolToIntIntermediateLambda(5))
    	assertTrue(node + " is not extracted.", extractorResults contains node)
    
    val codeGenerator = new CodeGenerator
    
    val expressions = extractorResults.map(codeGenerator(_)).toSet
    
    assertTrue(expressions contains boolInv)
    assertTrue(expressions contains inv1WithBoolInv)
    assertTrue(expressions contains inv1WithInt)
    assertTrue(expressions contains inv2WithInt)
    assertTrue(expressions contains inv3WithInt)  
    assertTrue(expressions contains inv2WithBoolInv)    
    assertTrue(expressions contains inv3WithBoolInv)      
  }

}