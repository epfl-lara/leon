/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.purescala

import leon.test._
import leon.purescala.Expressions._

class InliningSuite extends LeonTestSuiteWithProgram with helpers.ExpressionsDSL {
  val sources = List(
    """|
       |import leon.lang._
       |import leon.annotation._
       |
       |object InlineGood {
       |
       |  @inline
       |  def foo(a: BigInt) = true
       |
       |  def bar(a: BigInt) = foo(a)
       |
       |} """.stripMargin,

    """|import leon.lang._
       |import leon.annotation._
       |
       |object InlineBad {
       |
       |  @inline
       |  def foo(a: BigInt): BigInt = if (a > 42) foo(a-1) else 0
       |
       |  def bar(a: BigInt) = foo(a)
       |
       |}""".stripMargin,

    """|import leon.lang._
       |import leon.annotation._
       |
       |object InlineGood2 {
       |
       |  @inline
       |  def foo(a: BigInt) = true
       |
       |  @inline
       |  def bar(a: BigInt) = foo(a)
       |
       |  def baz(a: BigInt) = bar(a)
       |
       |}""".stripMargin,

    """|import leon.lang._
       |import leon.annotation._
       |
       |object InlineSpecs {
       |
       |  @inline
       |  def foo(a: BigInt) = {
       |    require(a > 42)
       |    true
       |  } ensuring (_ => false)
       |
       |  @inline
       |  def bar(a: BigInt) = {
       |    require(a > 0)
       |    foo(a)
       |  } ensuring (_ => true)
       |
       |  def baz(a: BigInt) = bar(a)
       |
       |}""".stripMargin
  )


  test("Simple Inlining") { implicit fix =>
    assert(funDef("InlineGood.bar").fullBody == BooleanLiteral(true), "Function not inlined?")
  }

  test("Recursive Inlining") { implicit fix =>
    funDef("InlineBad.bar").fullBody match {
      case FunctionInvocation(tfd, args) if tfd.id.name == "foo" => // OK, not inlined
      case b =>
        fail(s"Resultig body should be a call to 'foo', got '$b'")
    }
  }

  test("Double Inlining") { implicit fix =>
    assert(funDef("InlineGood2.baz").fullBody == BooleanLiteral(true), "Inlined function invocation not inlined in turn?")
  }

  test("Inlining specs") { implicit fix =>
    import leon.purescala.ExprOps.count
    val matcher = (e: Expr) => e match {
      case Assert(_, _, _) => 1
      case _ => 0
    }
    println(funDef("InlineSpecs.baz"))
    assert(count(matcher)(funDef("InlineSpecs.baz").fullBody) == 4, "Inlining failed on specs")
  }


}
