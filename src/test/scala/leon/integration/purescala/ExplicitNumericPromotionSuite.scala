/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.purescala

import leon.test._
import leon.purescala.Expressions._
import leon.purescala.Types._

class ExplicitNumericPromotionSuite extends LeonTestSuiteWithProgram with helpers.ExpressionsDSL {
  val sources = List(
    """|object Ints {
       |
       |  def foo(i: Int, j: Int) = i + j
       |
       |  def bar(i: Int, j: Int) = i & j
       |
       |  def gun(i: Int) = -i
       |
       |} """.stripMargin,

    """|object IntByte {
       |
       |  def foo(i: Int, j: Byte) = i + j
       |
       |  def bar(i: Int, j: Byte) = i & j
       |
       |} """.stripMargin,

    """|object ByteInt {
       |
       |  def foo(i: Byte, j: Int) = i + j
       |
       |  def bar(i: Byte, j: Int) = i & j
       |
       |} """.stripMargin,

    """|object Bytes {
       |
       |  def foo(i: Byte, j: Byte) = i + j
       |
       |  def bar(i: Byte, j: Byte) = i & j
       |
       |  def gun(i: Byte) = -i
       |
       |} """.stripMargin,

    """|object ExplicitCast {
       |
       |  def foo(i: Int) = bar(i.toByte)
       |
       |  def bar(b: Byte) = b
       |
       |} """.stripMargin,

    """|object ImplicitCast {
       |
       |  def foo(b: Byte) = bar(b) // implicit b.toInt here
       |
       |  def bar(i: Int) = i
       |
       |} """.stripMargin
  )


  test("No redundant cast on arithmetic int operations") { implicit fix =>
    funDef("Ints.foo").fullBody match {
      case BVPlus(Variable(i), Variable(j)) if i.name == "i" && j.name == "j" => // OK
      case b =>
        fail(s"Resultig body should be a simple BV addition, got '$b'")
    }

    funDef("Ints.bar").fullBody match {
      case BVAnd(Variable(i), Variable(j)) if i.name == "i" && j.name == "j" => // OK
      case b =>
        fail(s"Resulting body should be a simple BV and, got '$b'")
    }

    funDef("Ints.gun").fullBody match {
      case BVUMinus(Variable(i)) if i.name == "i" => // OK
      case b =>
        fail(s"Resulting body should be a simple BV unary minus, got '$b'")
    }
  }

  test("Explicit cast on binary arithmetic operations involving ints & bytes") { implicit fix =>
    funDef("IntByte.foo").fullBody match {
      case BVPlus(Variable(i), Variable(j)) if i.name == "i" && j.name == "j" =>
        fail(s"No explicit cast were inserted")
      case BVPlus(Variable(i), BVWideningCast(Variable(j), Int32Type)) if i.name == "i" && j.name == "j" => // OK
      case b =>
        fail(s"Resultig body should be a BV addition with explicit cast, got '$b'")
    }

    funDef("IntByte.bar").fullBody match {
      case BVAnd(Variable(i), BVWideningCast(Variable(j), Int32Type)) if i.name == "i" && j.name == "j" => // OK
      case b =>
        fail(s"Resulting body should be a BV and with explicit cast, got '$b'")
    }

    // Test symmetry
    funDef("ByteInt.foo").fullBody match {
      case BVPlus(Variable(i), Variable(j)) if i.name == "i" && j.name == "j" =>
        fail(s"No explicit cast were inserted")
      case BVPlus(BVWideningCast(Variable(i), Int32Type), Variable(j)) if i.name == "i" && j.name == "j" => // OK
      case b =>
        fail(s"Resultig body should be a BV addition with explicit cast, got '$b'")
    }

    funDef("ByteInt.bar").fullBody match {
      case BVAnd(BVWideningCast(Variable(i), Int32Type), Variable(j)) if i.name == "i" && j.name == "j" => // OK
      case b =>
        fail(s"Resulting body should be a BV and with explicit cast, got '$b'")
    }
  }

  test("Explicit cast on arithmetic operations involving only bytes") { implicit fix =>
    funDef("Bytes.foo").fullBody match {
      case BVPlus(BVWideningCast(Variable(i), Int32Type), BVWideningCast(Variable(j), Int32Type))
        if i.name == "i" && j.name == "j" => // OK
      case b =>
        fail(s"Resultig body should be a BV addition  with widening cast, got '$b'")
    }

    funDef("Bytes.bar").fullBody match {
      case BVAnd(BVWideningCast(Variable(i), Int32Type), BVWideningCast(Variable(j), Int32Type))
        if i.name == "i" && j.name == "j" => // OK
      case b =>
        fail(s"Resulting body should be a BV and with widening cast, got '$b'")
    }

    funDef("Bytes.gun").fullBody match {
      case BVUMinus(BVWideningCast(Variable(i), Int32Type)) if i.name == "i" => // OK
      case b =>
        fail(s"Resulting body should be a BV unary minus with widening cast, got '$b'")
    }
  }

  test("Explicit casts should be preserved") { implicit fix =>
    funDef("ExplicitCast.foo").fullBody match {
      case FunctionInvocation(tfd, Seq(BVNarrowingCast(Variable(i), Int8Type)))
        if tfd.id.name == "bar" && i.name == "i" => // OK
      case b =>
        fail(s"Resultig body should be a function call with one narrowing cast on its only argument, got '$b'")
    }
  }

  test("Implicit casts should be preserved") { implicit fix =>
    funDef("ImplicitCast.foo").fullBody match {
      case FunctionInvocation(tfd, Seq(BVWideningCast(Variable(b), Int32Type)))
        if tfd.id.name == "bar" && b.name == "b" => // OK
      case b =>
        fail(s"Resultig body should be a function call with one widening cast on its only argument, got '$b'")
    }
  }

}

