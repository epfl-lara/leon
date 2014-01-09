package leon.test.condabd
package refinement

import scala.util.Random

import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen

import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._

import leon.synthesis.condabd.insynth.leon._
import leon.synthesis.condabd.refinement._

import util.Scaffold._

class VariableRefinerTest extends FunSpec with GivenWhenThen {
  
  import RefinementExamples._
  
  describe("A variable refiner with list ADT") {
    
    it("should refine if variable is not Nil") {
      
      Given("a VariableRefiner based on structure")
      val variableRefiner = new VariableRefinerStructure(
        directSubclassMap, Seq(listLeonDeclaration), classMap, reporter
      )
      
      Then("it should return appropriate id And class def")
      expectResult(Some((listVal.id, nilAbstractClass))) {
      	variableRefiner.getIdAndClassType(CaseClassInstanceOf(nilAbstractClass, listVal))
      }
      And("return None for some unknown expression")
      expectResult(None) {
      	variableRefiner.getIdAndClassType(listVal)
      }
      
      Then("declarations should be updated accordingly")
      val allDeclarations = List(listLeonDeclaration)
	    expectResult((true,
        LeonDeclaration(
					ImmediateExpression( listVal + "." + headId,
            CaseClassSelector(consAbstractClass, listVal, headId) ), 
					  TypeTransformer(Int32Type), Int32Type
				) :: 
				LeonDeclaration(
					listLeonDeclaration.expression, TypeTransformer(consAbstractClass), consAbstractClass
				) :: Nil
  		)) {
        variableRefiner.refine(CaseClassInstanceOf(nilAbstractClass, listVal),
	        BooleanLiteral(true),
	        allDeclarations
        )
      } 
	    
      And("after 2nd consequtive call, nothing should happen")   
	    expectResult((false, allDeclarations)) {
        variableRefiner.refine(CaseClassInstanceOf(nilAbstractClass, listVal),
        BooleanLiteral(true),
        allDeclarations)
      } 
    }
    
  }
  
}
