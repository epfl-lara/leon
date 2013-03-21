package insynth.reconstruction

import org.junit.{ Test, Ignore, BeforeClass, AfterClass }
import org.junit.Assert._

import insynth.reconstruction.codegen.CodeGenerator
import insynth.Config

import leon.purescala.Definitions.{ FunDef, VarDecl, Program, ObjectDef }
import leon.purescala.Common.{ FreshIdentifier }
import leon.purescala.TypeTrees._
import leon.purescala.Trees.{ Variable => LeonVariable, _ }

import insynth.testutil.{ CommonProofTrees, CommonDeclarations, CommonLeonExpressions, CommonUtils }

class ReconstructorTest {

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
    
    assertTrue(expressions contains boolInv)
    assertTrue(expressions contains inv1WithBoolInv)
    assertTrue(expressions contains inv1WithInt)
    assertTrue(expressions contains inv2WithInt)
    assertTrue(expressions contains inv3WithInt)  
    assertTrue(expressions contains inv2WithBoolInv)    
    assertTrue(expressions contains inv3WithBoolInv)      
  }
  
  @Test
  def treeIntToIntBothOrdered {
    val queryNode = exampleIntToIntBoth
    
    val expStream = Reconstructor(queryNode, codegen, true)
    
    val expressions = assertTake(expStream, 20).map(_.snippet)
    
    val listOfExpressions = List(boolInv, inv1WithInt, inv1WithBoolInv, inv2WithInt,
      inv3WithInt, inv2WithBoolInv, inv3WithBoolInv)
    
    for (exp <- listOfExpressions)
    	assertTrue(expressions.toSet contains exp)
    	
    val listOfExpressionsOrder = List(boolInv, inv1WithBoolInv, inv2WithInt,
      inv2WithBoolInv, inv3WithBoolInv)
    
    for (ind <- 0 until listOfExpressionsOrder.size - 1)
      assertTrue("Expression " + listOfExpressionsOrder(ind) + " (position " + expressions.indexOf(listOfExpressionsOrder(ind)) +
        ") should occur before expression " + listOfExpressionsOrder(ind+1) + " (position " + expressions.indexOf(listOfExpressionsOrder(ind + 1)) + ")",
        expressions.indexOf(listOfExpressionsOrder(ind)) < expressions.indexOf(listOfExpressionsOrder(ind+1)))
      
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
