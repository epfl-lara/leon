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
  val listAbstractClassDef = new AbstractClassDef(listClassId, Seq())
  val listAbstractClass = new AbstractClassType(listAbstractClassDef, Seq())
  
  val nilClassId = FreshIdentifier("Nil")
  val nilAbstractClassDef = new CaseClassDef(nilClassId, Seq()).setParent(listAbstractClass)
  val nilAbstractClass = new CaseClassType(nilAbstractClassDef, Seq())
  
  val consClassId = FreshIdentifier("Cons")
  val consAbstractClassDef = new CaseClassDef(consClassId, Seq()).setParent(listAbstractClass)
  val headId = FreshIdentifier("head").setType(Int32Type)
  consAbstractClassDef.fields = Seq(VarDecl(headId, Int32Type))
  val consAbstractClass = new CaseClassType(consAbstractClassDef, Seq())
  
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
      AbstractClassType(listAbstractClassDef, Seq()) ->
        Set(CaseClassType(nilAbstractClassDef, Seq()), CaseClassType(consAbstractClassDef, Seq()))
    )
  
    val classMap: Map[Identifier, ClassType] = Map(
      listAbstractClassDef.id -> AbstractClassType(listAbstractClassDef, Seq()),
      nilAbstractClassDef.id -> CaseClassType(nilAbstractClassDef, Seq()),
      consAbstractClassDef.id -> CaseClassType(consAbstractClassDef, Seq())
    )
    
    (directSubclassMap, AbstractClassType(listAbstractClassDef, Seq()), classMap)
  }

}
