package insynth.testutil

import leon.purescala.Definitions.{ FunDef, VarDecl, Program, ObjectDef }
import leon.purescala.Common.{ FreshIdentifier }
import leon.purescala.TypeTrees._
import leon.purescala.Trees.{ Variable => _, _ }

object CommonLeonExpressions {

  import CommonDeclarations._
        
  val boolInv = FunctionInvocation(functionBoolToIntFunDef, List(booleanLiteral))
  val inv1WithBoolInv = FunctionInvocation(functionIntToIntFunDef, List(boolInv))
  val inv1WithInt = FunctionInvocation(functionIntToIntFunDef, List(intLiteral))
  val inv2WithInt = FunctionInvocation(functionIntToIntFunDef, List(inv1WithInt))
  val inv3WithInt = FunctionInvocation(functionIntToIntFunDef, List(inv2WithInt))
  val inv2WithBoolInv = FunctionInvocation(functionIntToIntFunDef, List(inv1WithBoolInv))
  val inv3WithBoolInv = FunctionInvocation(functionIntToIntFunDef, List(inv2WithBoolInv))

}