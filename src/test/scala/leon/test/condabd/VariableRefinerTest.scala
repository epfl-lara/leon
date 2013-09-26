package leon.test.condabd

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
  
  val listClassId = FreshIdentifier("List")
  val listAbstractClassDef = new AbstractClassDef(listClassId)
  val listAbstractClass = new AbstractClassType(listAbstractClassDef)
  
  val nilClassId = FreshIdentifier("Nil")
  val nilAbstractClassDef = new CaseClassDef(nilClassId).setParent(listAbstractClassDef)
  val nilAbstractClass = new CaseClassType(nilAbstractClassDef)
  
  val consClassId = FreshIdentifier("Cons")
  val consAbstractClassDef = new CaseClassDef(consClassId).setParent(listAbstractClassDef)
  val headId = FreshIdentifier("head").setType(Int32Type)
  consAbstractClassDef.fields = Seq(VarDecl(headId, Int32Type))
  val consAbstractClass = new CaseClassType(consAbstractClassDef)
  
  val directSubclassMap: Map[ClassType, Set[ClassType]] = Map(
    listAbstractClass -> Set(nilAbstractClass, consAbstractClass)
  )
  
  val listVal = Variable(FreshIdentifier("tempVar"))
  val listLeonDeclaration = LeonDeclaration(
    ImmediateExpression( "tempVar", listVal ), 
    TypeTransformer(listAbstractClass), listAbstractClass
  )
  
  val classMap: Map[Identifier, ClassType] = Map(
    listClassId -> listAbstractClass,
    nilClassId -> nilAbstractClass,
    consClassId -> consAbstractClass
  ) 
  
  describe("A variable refiner with list ADT") {
    
    it("should refine if variable is not Nil") {
      
      Given("a VariableRefiner")
      val variableRefiner = new VariableRefiner(
        directSubclassMap, Seq(listLeonDeclaration), classMap, reporter
      )
      
      Then("it should return appropriate id And class def")
      expectResult(Some((listVal.id, nilAbstractClassDef))) {
      	variableRefiner.getIdAndClassDef(CaseClassInstanceOf(nilAbstractClassDef, listVal))
      }
      And("return None for some unknown expression")
      expectResult(None) {
      	variableRefiner.getIdAndClassDef(listVal)
      }
      
      Then("declarations should be updated accordingly")
      val allDeclarations = List(listLeonDeclaration)
	    expectResult((true,
        LeonDeclaration(
					ImmediateExpression( listVal + "." + headId,
            CaseClassSelector(consAbstractClassDef, listVal, headId) ), 
					  TypeTransformer(Int32Type), Int32Type
				) :: 
				LeonDeclaration(
					listLeonDeclaration.expression, TypeTransformer(consAbstractClass), consAbstractClass
				) :: Nil
  		)) {
        variableRefiner.checkRefinements(CaseClassInstanceOf(nilAbstractClassDef, listVal),
	        BooleanLiteral(true),
	        allDeclarations
        )
      } 
	    
      And("after 2nd consequtive call, nothing should happen")   
	    expectResult((false, allDeclarations)) {
        variableRefiner.checkRefinements(CaseClassInstanceOf(nilAbstractClassDef, listVal),
        BooleanLiteral(true),
        allDeclarations)
      } 
    }
    
  }
  
}