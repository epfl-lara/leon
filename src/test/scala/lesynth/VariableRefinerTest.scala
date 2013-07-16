package lesynth

import scala.util.Random

import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen

import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._

import insynth.leon._

import lesynth.refinement._

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
      
      given("a VariableRefiner")
      val variableRefiner = new VariableRefiner(
        directSubclassMap, Seq(listLeonDeclaration), classMap
      )
      
      then("it should return appropriate id and class def")
      expect(Some((listVal.id, nilAbstractClassDef))) {
      	variableRefiner.getIdAndClassDef(CaseClassInstanceOf(nilAbstractClassDef, listVal))
      }
      and("return None for some unknown expression")
      expect(None) {
      	variableRefiner.getIdAndClassDef(listVal)
      }
      
      then("declarations should be updated accordingly")
      val allDeclarations = List(listLeonDeclaration)
	    expect((true,
        LeonDeclaration(
					ImmediateExpression( "Field(" + consAbstractClassDef + "." + headId + ")",
            CaseClassSelector(consAbstractClassDef, listVal, headId) ), 
					  TypeTransformer(Int32Type), Int32Type
				) :: 
				LeonDeclaration(
					listLeonDeclaration.expression, TypeTransformer(consAbstractClass), consAbstractClass
				) :: Nil
  		)) {
        variableRefiner.checkRefinements(CaseClassInstanceOf(nilAbstractClassDef, listVal),
        BooleanLiteral(true),
        allDeclarations)
      } 
	    
      and("after 2nd consequtive call, nothing should happen")   
	    expect((false, allDeclarations)) {
        variableRefiner.checkRefinements(CaseClassInstanceOf(nilAbstractClassDef, listVal),
        BooleanLiteral(true),
        allDeclarations)
      } 
    }
    
  }
  
}