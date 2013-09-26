package leon.test.condabd.insynth
package reconstruction

import org.junit.Assert._
import org.junit.{ Test, Ignore }
import org.scalatest.junit.JUnitSuite

import leon.synthesis.condabd.insynth.reconstruction.codegen.CodeGenerator

import _root_.leon.purescala.Trees._

import testutil.{ CommonLambda, CommonDeclarations }

// NOTE function cannot return function in Leon, no need to test that

class CodeGeneratorTest extends JUnitSuite {
    
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
        
  }
  
}