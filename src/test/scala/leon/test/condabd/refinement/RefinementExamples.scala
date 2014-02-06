package leon.test.condabd.refinement

import scala.util.Random

import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen

import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._

import leon.synthesis.condabd.insynth.leon._
import leon.synthesis.condabd.refinement._

object RefinementExamples {   
  
  val listClassId = FreshIdentifier("List")
  val listAbstractClassDef = new AbstractClassDef(listClassId, Nil, None)
  val listAbstractClass = new AbstractClassType(listAbstractClassDef, Nil)
  
  val nilClassId = FreshIdentifier("Nil")
  val nilAbstractClassDef = new CaseClassDef(nilClassId, Nil, None, false)
  val nilAbstractClass = new CaseClassType(nilAbstractClassDef, Nil)
  
  val consClassId = FreshIdentifier("Cons")
  val consAbstractClassDef = new CaseClassDef(consClassId, Nil, None, false)
  val headId = FreshIdentifier("head").setType(Int32Type)
  consAbstractClassDef.setFields(Seq(ValDef(headId, Int32Type)))
  val consAbstractClass = new CaseClassType(consAbstractClassDef, Nil)
  
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
  
  def buildClassMap(program: Program) = {
    val listAbstractClassDef = program.definedClasses.find(_.id.name == "List").
      get.asInstanceOf[AbstractClassDef]
    val listAbstractClass = AbstractClassType(listAbstractClassDef, Nil)
    
    val nilAbstractClassDef = program.definedClasses.find(_.id.name == "Nil").
      get.asInstanceOf[CaseClassDef]
    val nilAbstractClass = CaseClassType(nilAbstractClassDef, Nil)
    
    val consAbstractClassDef = program.definedClasses.find(_.id.name == "Cons").
      get.asInstanceOf[CaseClassDef]
    val consAbstractClass = CaseClassType(consAbstractClassDef, Nil)
        
    val directSubclassMap: Map[ClassType, Set[ClassType]] = Map(
      listAbstractClass ->
        Set(nilAbstractClass, consAbstractClass)
    )
  
    val classMap: Map[Identifier, ClassType] = Map(
      listAbstractClassDef.id -> listAbstractClass,
      nilAbstractClassDef.id -> nilAbstractClass,
      consAbstractClassDef.id -> consAbstractClass
    )
    
    (directSubclassMap, listAbstractClass, classMap)
  }

}
