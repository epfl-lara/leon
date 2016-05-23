/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package unit.utils

import purescala.Common._
import purescala.Definitions._
import purescala.ExprOps._
import purescala.Expressions._
import purescala.FunctionClosure
import purescala.Types._
import test._
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

  test("close captures enclosing require if needed") {
    val nested = new FunDef(FreshIdentifier("nested"), Seq(), Seq(ValDef(y.id)), IntegerType)
    nested.body = Some(Plus(x, y))

    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(Require(GreaterEquals(x, bi(0)), LetDef(Seq(nested), x)))

    val cfds = FunctionClosure.close(fd)
    assert(cfds.size === 2)

    cfds.foreach(cfd => {
      if(cfd.id.name == "f") {
        assert(cfd.returnType === fd.returnType)
        assert(cfd.params.size === fd.params.size)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "nested") {
        assert(cfd.returnType === nested.returnType)
        assert(cfd.params.size === 2)
        assert(freeVars(cfd).isEmpty)
        assert(cfd.precondition != None)
        //next assert is assuming that the function closures always adds paramters at the end of the parameter list
        cfd.precondition.foreach(pre => assert(pre == GreaterEquals(cfd.params.last.toVariable, bi(0)))) 
      } else {
        fail("Unexpected fun def: " + cfd)
      }
    })
  }

  test("close captures transitive dependencies within path") {
    val x2 = FreshIdentifier("x2", IntegerType).toVariable
    val x3 = FreshIdentifier("x3", IntegerType).toVariable

    val nested = new FunDef(FreshIdentifier("nested"), Seq(), Seq(ValDef(y.id)), IntegerType)
    nested.body = Some(Plus(y, x3))


    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(
      Let(x2.id, Plus(x, bi(1)),
        Let(x3.id, Plus(x2, bi(1)),
          LetDef(Seq(nested), x)))
    )

    val cfds = FunctionClosure.close(fd)
    assert(cfds.size === 2)

    cfds.foreach(cfd => {
      if(cfd.id.name == "f") {
        assert(cfd.returnType === fd.returnType)
        assert(cfd.params.size === fd.params.size)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "nested") {
        assert(cfd.returnType === nested.returnType)
        assert(cfd.params.size === 2)
        assert(freeVars(cfd).isEmpty)
      } else {
        fail("Unexpected fun def: " + cfd)
      }
    })
  }

  test("close captures transitive dependencies within path but not too many") {
    val x2 = FreshIdentifier("x2", IntegerType).toVariable
    val x3 = FreshIdentifier("x3", IntegerType).toVariable
    val x4 = FreshIdentifier("x4", IntegerType).toVariable

    val nested = new FunDef(FreshIdentifier("nested"), Seq(), Seq(ValDef(y.id)), IntegerType)
    nested.body = Some(Plus(y, x4))


    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id), ValDef(z.id)), IntegerType)
    fd.body = Some(
      Let(x2.id, Plus(x, bi(1)),
        Let(x3.id, Plus(z, bi(1)),
          Let(x4.id, Plus(x2, bi(1)),
            LetDef(Seq(nested), x))))
    )

    val cfds = FunctionClosure.close(fd)
    assert(cfds.size === 2)

    cfds.foreach(cfd => {
      if(cfd.id.name == "f") {
        assert(cfd.returnType === fd.returnType)
        assert(cfd.params.size === fd.params.size)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "nested") {
        assert(cfd.returnType === nested.returnType)
        assert(cfd.params.size === 2)
        assert(freeVars(cfd).isEmpty)
      } else {
        fail("Unexpected fun def: " + cfd)
      }
    })
  }

  test("close captures enclosing require of callee functions") {
    val callee = new FunDef(FreshIdentifier("callee"), Seq(), Seq(), IntegerType)
    callee.body = Some(x)

    val caller = new FunDef(FreshIdentifier("caller"), Seq(), Seq(), IntegerType)
    caller.body = Some(FunctionInvocation(callee.typed, Seq()))

    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(x.id)), IntegerType)
    fd.body = Some(Require(GreaterEquals(x, bi(0)), LetDef(Seq(callee, caller), x)))

    val cfds = FunctionClosure.close(fd)
    assert(cfds.size === 3)

    cfds.foreach(cfd => {
      if(cfd.id.name == "f") {
        assert(cfd.returnType === fd.returnType)
        assert(cfd.params.size === fd.params.size)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "callee") {
        assert(cfd.returnType === callee.returnType)
        assert(cfd.params.size === 1)
        assert(freeVars(cfd).isEmpty)
      } else if(cfd.id.name == "caller") {
        assert(cfd.returnType === caller.returnType)
        assert(cfd.params.size === 1)
        assert(freeVars(cfd).isEmpty)
        assert(cfd.precondition != None)
        //next assert is assuming that the function closures always adds paramters at the end of the parameter list
        cfd.precondition.foreach(pre => assert(pre == GreaterEquals(cfd.params.last.toVariable, bi(0)))) 
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
