/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.purescala

import leon._
import purescala.Definitions._
import purescala.DefOps._
import purescala.Expressions._
import frontends.scalac._
import utils._
import leon.test.LeonTestSuite

class InliningSuite extends LeonTestSuite {
  private def parseProgram(str: String): (Program, LeonContext) = {
    val context = createLeonContext()

    val pipeline =
      TemporaryInputPhase andThen
      ExtractionPhase andThen
      PreprocessingPhase

    val program = pipeline.run(context)((str, Nil))

    (program, context)
  }

  test("Simple Inlining") {
    val (pgm, ctx) = parseProgram(
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
         |} """.stripMargin)

    val bar = pgm.lookup("InlineGood.bar").collect { case fd: FunDef => fd }.get

    assert(bar.fullBody == BooleanLiteral(true), "Function not inlined?")
  }

  test("Recursive Inlining") {
    val (pgm, ctx) = parseProgram(
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
         |}""".stripMargin)

     assert(ctx.reporter.warningCount > 0, "Warning received for the invalid inline")
  }
}
