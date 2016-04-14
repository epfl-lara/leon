/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.utils

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.TypeOps.isSubtypeOf
import leon.purescala.Definitions._
import leon.purescala.ExprOps._
import leon.purescala.FunctionClosure

import org.scalatest._

class FunctionClosureSuite extends FunSuite with helpers.ExpressionsDSL {

  val fd1 = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd1.body = Some(x)

  test("close does not modify a function without nested functions") {
    val cfd1 = FunctionClosure.close(fd1)
    assert(cfd1.size === 1)
    assert(fd1 === cfd1.head)
    assert(fd1.body === cfd1.head.body)
  }

}
