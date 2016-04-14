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

  test("close does not capture param from parent if not needed") {
    val nested = new FunDef(FreshIdentifier("nested"), Seq(), Seq(ValDef(y.id)), IntegerType)
    nested.body = Some(y)

    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(LetDef(Seq(nested), x))

    val cfds = FunctionClosure.close(fd)
    assert(cfds.size === 2)

    cfds.foreach(cfd => {
      if(cfd.id.name == "f") {
        assert(cfd.returnType === fd.returnType)
        assert(cfd.params.size === fd.params.size)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "nested") {
        assert(cfd.returnType === nested.returnType)
        assert(cfd.params.size === nested.params.size)
        assert(freeVars(cfd).isEmpty)
      } else {
        fail("Unexpected fun def: " + cfd)
      }
    })


    val nested2 = new FunDef(FreshIdentifier("nested"), Seq(), Seq(ValDef(y.id)), IntegerType)
    nested2.body = Some(y)

    val fd2 = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd2.body = Some(Let(z.id, Plus(x, bi(1)), LetDef(Seq(nested2), x)))

    val cfds2 = FunctionClosure.close(fd2)
    assert(cfds2.size === 2)

    cfds2.foreach(cfd => {
      if(cfd.id.name == "f") {
        assert(cfd.returnType === fd2.returnType)
        assert(cfd.params.size === fd2.params.size)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "nested") {
        assert(cfd.returnType === nested2.returnType)
        assert(cfd.params.size === nested2.params.size)
        assert(freeVars(cfd).isEmpty)
      } else {
        fail("Unexpected fun def: " + cfd)
      }
    })
  }

  test("close does not capture enclosing require if not needed") {
    val nested = new FunDef(FreshIdentifier("nested"), Seq(), Seq(ValDef(y.id)), IntegerType)
    nested.body = Some(y)

    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(Require(GreaterEquals(x, bi(0)), Let(z.id, Plus(x, bi(1)), LetDef(Seq(nested), x))))

    val cfds = FunctionClosure.close(fd)
    assert(cfds.size === 2)

    cfds.foreach(cfd => {
      if(cfd.id.name == "f") {
        assert(cfd.returnType === fd.returnType)
        assert(cfd.params.size === fd.params.size)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "nested") {
        assert(cfd.returnType === nested.returnType)
        assert(cfd.params.size === nested.params.size)
        assert(freeVars(cfd).isEmpty)
      } else {
        fail("Unexpected fun def: " + cfd)
      }
    })


    val deeplyNested2 = new FunDef(FreshIdentifier("deeplyNested"), Seq(), Seq(ValDef(z.id)), IntegerType)
    deeplyNested2.body = Some(Require(GreaterEquals(x, bi(0)), z))

    val nested2 = new FunDef(FreshIdentifier("nested"), Seq(), Seq(ValDef(y.id)), IntegerType)
    nested2.body = Some(LetDef(Seq(deeplyNested2), FunctionInvocation(deeplyNested2.typed, Seq(y))))

    val fd2 = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd2.body = Some(Require(GreaterEquals(x, bi(0)),
                    LetDef(Seq(nested2), FunctionInvocation(nested2.typed, Seq(x)))))

    val cfds2 = FunctionClosure.close(fd2)
    assert(cfds2.size === 3)

    cfds2.foreach(cfd => {
      if(cfd.id.name == "f") {
        assert(cfd.returnType === fd2.returnType)
        assert(cfd.params.size === fd2.params.size)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "nested") {
        assert(cfd.returnType === nested2.returnType)
        assert(cfd.params.size === 2)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "deeplyNested") {
        assert(cfd.returnType === deeplyNested2.returnType)
        assert(cfd.params.size === 2)
        assert(freeVars(cfd).isEmpty)
      } else {
        fail("Unexpected fun def: " + cfd)
      }
    })
  }

  private def freeVars(fd: FunDef): Set[Identifier] = variablesOf(fd.fullBody) -- fd.paramIds

}
