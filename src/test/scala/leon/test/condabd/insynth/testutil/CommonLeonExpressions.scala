/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.condabd.insynth.testutil

import leon.purescala.Definitions.{ FunDef, ValDef, Program, ModuleDef }
import leon.purescala.Common.{ FreshIdentifier }
import leon.purescala.TypeTrees._
import leon.purescala.Trees.{ Variable => _, _ }

object CommonLeonExpressions {

  import CommonDeclarations._
        
  val boolToInt = functionBoolToIntFunDef.typed
  val intToInt  = functionIntToIntFunDef.typed

  val inv1boolInv = FunctionInvocation(boolToInt, List(booleanLiteral))
  val inv2WithBoolInv = FunctionInvocation(intToInt, List(inv1boolInv))
  val inv1WithInt = FunctionInvocation(intToInt, List(intLiteral))
  val inv2WithInt = FunctionInvocation(intToInt, List(inv1WithInt))
  val inv3WithInt = FunctionInvocation(intToInt, List(inv2WithInt))
  val inv3WithBoolInv = FunctionInvocation(intToInt, List(inv2WithBoolInv))
  val inv4WithBoolInv = FunctionInvocation(intToInt, List(inv3WithBoolInv))
  val inv4WithInt = FunctionInvocation(intToInt, List(inv3WithInt))

}
