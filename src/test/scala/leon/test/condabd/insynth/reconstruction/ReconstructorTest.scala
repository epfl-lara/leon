package leon.test.condabd.insynth
package reconstruction

import org.junit.{ Test, Ignore, BeforeClass, AfterClass }
import org.junit.Assert._
import org.scalatest.junit.JUnitSuite

import leon.synthesis.condabd.insynth.reconstruction.codegen.CodeGenerator
import leon.synthesis.condabd.insynth.reconstruction._

import leon.purescala.Definitions.{ FunDef, VarDecl, Program, ObjectDef }
import leon.purescala.Common.{ FreshIdentifier }
import leon.purescala.TypeTrees._
import leon.purescala.Trees.{ Variable => LeonVariable, _ }

import testutil.{ CommonProofTrees, CommonDeclarations, CommonLeonExpressions, CommonUtils }

class ReconstructorTest extends JUnitSuite {

  import CommonDeclarations._
  import CommonProofTrees._
  import CommonLeonExpressions._
  import CommonUtils._
  
  val codegen = new CodeGenerator
  
  @Test
  def treeBoolToInt {
    val (queryNode, query) = exampleBoolToInt
    
    val expStream = Reconstructor(queryNode, codegen)
    
    assertEquals(1, expStream.size)
    
    val codeGenResult = expStream.head
    
    assertEquals(FunctionInvocation(functionBoolToIntFunDef, List(BooleanLiteral(false))), codeGenResult.snippet)
    assertEquals(0f, codeGenResult.weight, 0f)    
  }
  
  @Test
  def treeIntToIntBoth {
    val queryNode = exampleIntToIntBoth
    
    val expStream = Reconstructor(queryNode, codegen)
    
    val expressions = expStream.map(_.snippet).take(20).toSet
    
    assertTrue(expressions contains inv1boolInv)
    assertTrue(expressions contains inv2WithBoolInv)
    assertTrue(expressions contains inv1WithInt)
    assertTrue(expressions contains inv2WithInt)
    assertTrue(expressions contains inv3WithInt)  
    assertTrue(expressions contains inv3WithBoolInv)    
    assertTrue(expressions contains inv4WithBoolInv)  
    assertTrue(expressions contains inv4WithInt)   
  }
  
  @Test
  def treeIntToIntBothOrdered {
    val queryNode = exampleIntToIntBoth
    
    val expStream = Reconstructor(queryNode, codegen, true)
    
    val expressions = assertTake(expStream, 20).map(_.snippet)
    
    val listOfExpressions = List(inv1boolInv, inv1WithInt, inv2WithBoolInv, inv2WithInt,
      inv3WithInt, inv3WithBoolInv, inv4WithBoolInv, inv4WithInt)
    
    for (exp <- listOfExpressions)
    	assertTrue(expressions.toSet contains exp)
    	
    val listOfExpressionsOrder = List(
      List(inv1boolInv, inv1WithInt),
      List(inv2WithBoolInv, inv2WithInt),
      List(inv3WithInt, inv3WithBoolInv),
      List(inv4WithBoolInv, inv4WithInt)
    )
    
    for (ind <- 0 until listOfExpressionsOrder.size - 1) {
      for( previousEl <- listOfExpressionsOrder(ind); nextEl <- listOfExpressionsOrder(ind + 1) )
	      assertTrue("Expression " + previousEl + " (position " + expressions.indexOf(previousEl) +
	        ") should occur before expression " + nextEl + " (position " + expressions.indexOf(nextEl) + ")",
	        expressions.indexOf(previousEl) < expressions.indexOf(nextEl))
    }
  	      
  }

}

//object ReconstructorTest {
//  
//  var useEnumerationOrdering: Boolean = _
//  
//  @BeforeClass
//  def saveFlag = {
//    useEnumerationOrdering = Config.useEnumerationOrdering
//    Config.useEnumerationOrdering = false
//  }
//  
//  @AfterClass
//  def restoreFlag = Config.useEnumerationOrdering = useEnumerationOrdering
//  
//}
