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
  
  def buildClassMap(program: Program) = {
    val listAbstractClassDef = program.definedClasses.find(_.id.name == "List").
      get.asInstanceOf[AbstractClassDef]
    
    val nilAbstractClassDef = program.definedClasses.find(_.id.name == "Nil").
      get.asInstanceOf[CaseClassDef]
    
    val consAbstractClassDef = program.definedClasses.find(_.id.name == "Cons").
      get.asInstanceOf[CaseClassDef]
        
    val directSubclassMap: Map[ClassType, Set[ClassType]] = Map(
      AbstractClassType(listAbstractClassDef) ->
        Set(CaseClassType(nilAbstractClassDef), CaseClassType(consAbstractClassDef))
    )
  
    val classMap: Map[Identifier, ClassType] = Map(
      listAbstractClassDef.id -> AbstractClassType(listAbstractClassDef),
      nilAbstractClassDef.id -> CaseClassType(nilAbstractClassDef),
      consAbstractClassDef.id -> CaseClassType(consAbstractClassDef)
    )
    
    (directSubclassMap, AbstractClassType(listAbstractClassDef), classMap)
  }

}