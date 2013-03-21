package insynth.reconstruction

import org.junit.Assert._
import org.junit.{ Test, Ignore }

import insynth.reconstruction.codegen.CodeGenerator

import leon.purescala.Trees._

import insynth.testutil.{ CommonLambda, CommonDeclarations }

// NOTE function cannot return function in Leon, no need to test that

class CodeGeneratorTest {
    
  import CommonLambda._
  import CommonDeclarations._
  
  val codeGenerator = new CodeGenerator
  
  @Test
  def testBooleanToIntIntermediateLambda {    
    val codeGenResult = codeGenerator(constructBooleanToIntIntermediateLambda.head)
      
    assertEquals(
      FunctionInvocation(functionBoolToIntFunDef, List(BooleanLiteral(false))),
      codeGenResult
    )
  }     
  
  @Test
  def testThreeParFunction {
    
    val generated =
	    for (intermediateTree <- constructThreeParFunctionIntermediateLambda(4))
	    	yield codeGenerator(intermediateTree)
    
    val baseCase = FunctionInvocation(threeParFunctionDef, List(IntLiteral(0), IntLiteral(0), BooleanLiteral(false)))
    
    val message = "Generated:\n" + generated.mkString("\n")
    
    assertTrue(baseCase + " not found. " + message, generated contains baseCase)
    
    val oneLevCase1 = FunctionInvocation(threeParFunctionDef, List(baseCase, IntLiteral(0), BooleanLiteral(false)))
    val oneLevCase2 = FunctionInvocation(threeParFunctionDef, List(baseCase, baseCase, BooleanLiteral(false)))
    
    assertTrue(oneLevCase1 + " not found. " + message, generated contains oneLevCase1)
    assertTrue(oneLevCase2 + " not found. " + message, generated contains oneLevCase2)
        
    val twoLevCase1 = FunctionInvocation(threeParFunctionDef, List(oneLevCase1, IntLiteral(0), BooleanLiteral(false)))
    val twoLevCase2 = FunctionInvocation(threeParFunctionDef, List(baseCase, oneLevCase2, BooleanLiteral(false)))
    
    assertTrue(twoLevCase1 + " not found. " + message, generated contains twoLevCase1)
    assertTrue(twoLevCase2 + " not found. " + message, generated contains twoLevCase2)
        
//    val threeLevCase1 = FunctionInvocation(threeParFunctionDef, List(oneLevCase1, twoLevCase2, BooleanLiteral(false)))
//    val threeLevCase2 = FunctionInvocation(threeParFunctionDef, List(twoLevCase2, threeLevCase1, BooleanLiteral(false)))
//    
//    assertTrue(threeLevCase1 + " not found. " + message, generated contains threeLevCase1)
//    assertTrue(threeLevCase2 + " not found. " + message, generated contains threeLevCase2)
  }
  
}