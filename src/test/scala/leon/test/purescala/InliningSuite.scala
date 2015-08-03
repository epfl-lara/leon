/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.purescala

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

    """ |import leon.lang._
       |import leon.annotation._
       |
       |object InlineBad {
       |
       |  @inline
       |  def foo(a: BigInt): BigInt = if (a > 42) foo(a-1) else 0
       |
       |  def bar(a: BigInt) = foo(a)
       |
       |}""".stripMargin
  )


  test("Simple Inlining") { implicit fix =>
    assert(funDef("InlineGood.bar").fullBody == BooleanLiteral(true), "Function not inlined?")
  }

  test("Recursive Inlining") { implicit ctx =>
    funDef("InlineBad.bar").fullBody match {
      case FunctionInvocation(tfd, args) if tfd.id.name == "foo" => // OK, not inlined
      case b =>
        fail(s"Resultig body should be a call to 'foo', got '$b'")
    }
  }
}
