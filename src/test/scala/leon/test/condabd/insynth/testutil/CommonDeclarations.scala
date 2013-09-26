package leon.test.condabd.insynth.testutil

import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet }

import org.junit.Assert._
import org.junit.Test
import org.junit.Ignore

import leon.synthesis.condabd.insynth.leon.loader.DeclarationFactory._
import leon.synthesis.condabd.insynth.leon._

import leon.purescala.Definitions.{ FunDef, VarDecl, Program, ObjectDef }
import leon.purescala.Common.{ FreshIdentifier }
import leon.purescala.TypeTrees._
import leon.purescala.Trees._

object CommonDeclarations {
  
  val booleanLiteral = BooleanLiteral(false)
        
  val booleanDeclaration = makeDeclaration(
      ImmediateExpression("false", booleanLiteral),
      BooleanType
  )
  
  val intLiteral = IntLiteral(0)
  
  val intDeclaration = makeDeclaration(
      ImmediateExpression("0", intLiteral),
      Int32Type
  )
  
  val unit = UnitLiteral
    
  val unitDeclaration = makeDeclaration(
      ImmediateExpression("unit", unit),
      UnitType
  )
  
  val functionBoolToIntFunDef = 
    new FunDef(
      FreshIdentifier("function1"),
      Int32Type,
      List( VarDecl(FreshIdentifier("var"), BooleanType))
    )
  
  val functionBoolToIntType =
    FunctionType(List(BooleanType), Int32Type)
      
  val functionBoolToIntDeclaration = makeDeclaration(
      NaryReconstructionExpression("function1", { args: List[Expr] => FunctionInvocation(functionBoolToIntFunDef, args) }), 
      functionBoolToIntType
    )     
      
  val functionFun1ToUnitFunDef = 
    new FunDef(
      FreshIdentifier("function2"),
      UnitType,
      List( VarDecl(FreshIdentifier("var"), functionBoolToIntType))
    )  
  
  val functionFun1ToUnitType =
    FunctionType(List(UnitType), functionBoolToIntType)
      
  val functionFun1ToUnitDeclaration = makeDeclaration(
      NaryReconstructionExpression("function2", { args: List[Expr] => FunctionInvocation(functionFun1ToUnitFunDef, args) }), 
      functionFun1ToUnitType
    )     
   
  val functionIntToIntType =
    FunctionType(List(Int32Type), Int32Type)
  
  val functionIntToIntFunDef= {
    val varId = FreshIdentifier("var")
    val varDec = VarDecl(varId, Int32Type)
    
    val funDef = new FunDef(
      FreshIdentifier("functionRec"),
      Int32Type,
      List( varDec )
    )
    
    funDef.body = Some(Variable(varId))
    
    funDef
  }
  
  val functionIntToIntDeclaration = makeDeclaration(
    NaryReconstructionExpression("functionRec", { args: List[Expr] => FunctionInvocation(functionIntToIntFunDef, args) }), 
    functionIntToIntType
  )
  
  val threeParFunctionType =
    FunctionType(List(Int32Type, Int32Type, BooleanType), Int32Type)
    
  val threeParFunctionDef = 
    new FunDef(
      FreshIdentifier("function3"),
      Int32Type,
      List(
        VarDecl(FreshIdentifier("var_1"), Int32Type),
        VarDecl(FreshIdentifier("var_2"), Int32Type),
        VarDecl(FreshIdentifier("var_3"), BooleanType)
      )
    )
  
  val threeParFunctionDeclaration = makeDeclaration(
      NaryReconstructionExpression("function3", { args: List[Expr] => FunctionInvocation(threeParFunctionDef, args) }), 
      threeParFunctionType
    )
  
}