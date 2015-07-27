/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Types._
import leon.purescala.Expressions._
import leon.purescala.TreeNormalizations._

class ArrayQuantifiersInstantiationSuite extends LeonTestSuite with ExpressionsBuilder {


  val arr = FreshIdentifier("arr", ArrayType(IntegerType)).toVariable
  val elId = FreshIdentifier("el", IntegerType)
  val allPos = ArrayForall(arr, 
                InfiniteIntegerLiteral(0), ArrayLength(arr), 
                Lambda(Seq(ValDef(elId)), GreaterEquals(elId.toVariable, InfiniteIntegerLiteral(0)))
               )

  val kId = FreshIdentifier("k", IntegerType)
  val oneNeg = LessThan(ArraySelect(arr, kId.toVariable), InfiniteIntegerLiteral(0))

  test("test") {

    ArrayQuantifiersInstantiation.instantiate(And(allPos, oneNeg))
  }
}
