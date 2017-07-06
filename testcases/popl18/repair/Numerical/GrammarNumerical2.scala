package leon
package grammar
import leon.collection._
import leon.collection.List._
import leon.collection.ListOps._
import leon.collection.ListSpecs._
import leon.lang.Set._
import leon.lang._
import leon.lang._
import leon.lang.synthesis._
import leon.math._
import annotation.grammar._

object GrammarNumerical {
  @label
  implicit class BigInt_1_IfExpr(val v : BigInt)
  
  @label
  implicit class BigInt_1_Minus(val v : BigInt)
  
  @label
  implicit class BigInt_1_Plus(val v : BigInt)
  
  @label
  implicit class BigInt_0_Division(val v : BigInt)
  
  @label
  implicit class BigInt_2_IfExpr(val v : BigInt)
  
  @label
  implicit class BigInt_0_Tuple(val v : BigInt)
  
  @label
  implicit class BigInt_0_Times(val v : BigInt)
  
  @label
  implicit class BigInt_1_Times(val v : BigInt)
  
  @label
  implicit class BigInt_0_Remainder(val v : BigInt)
  
  @label
  implicit class BigInt_0_LessThan(val v : BigInt)
  
  @label
  implicit class BigInt_1_Remainder(val v : BigInt)
  
  @label
  implicit class BigInt_0_Equals(val v : BigInt)
  
  @label
  implicit class BigInt_1_LessThan(val v : BigInt)
  
  @label
  implicit class BigInt_0_LessEquals(val v : BigInt)
  
  @label
  implicit class BigInt_0_FunctionInvocation(val v : BigInt)
  
  @label
  implicit class BigInt_TOPLEVEL(val v : BigInt)
  
  @label
  implicit class BigInt_0_Plus(val v : BigInt)
  
  @label
  implicit class BigInt_1_Equals(val v : BigInt)
  
  @label
  implicit class BigInt_1_Division(val v : BigInt)
  
  @label
  implicit class BigInt_1_FunctionInvocation(val v : BigInt)
  
  @label
  implicit class BigInt_1_Tuple(val v : BigInt)
  
  @label
  implicit class BigInt_1_LessEquals(val v : BigInt)
  
  @label
  implicit class BigInt_0_Minus(val v : BigInt)
  
  @label
  implicit class Boolean_0_Lambda(val v : Boolean)
  
  @label
  implicit class Boolean_0_Not(val v : Boolean)
  
  @label
  implicit class Boolean_0_And(val v : Boolean)
  
  @label
  implicit class Boolean_TOPLEVEL(val v : Boolean)
  
  @label
  implicit class Boolean_1_And(val v : Boolean)
  
  @label
  implicit class Boolean_0_IfExpr(val v : Boolean)
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$6(): BigInt_TOPLEVEL = BigInt(1)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$7(): BigInt_TOPLEVEL = BigInt(1024)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$8(): BigInt_TOPLEVEL = BigInt(0)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$9(): BigInt_TOPLEVEL = BigInt(128)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$10(): BigInt_TOPLEVEL = BigInt(12)
  
  @production(3)
  def pBigIntVariable$1(): BigInt_TOPLEVEL = variable[BigInt]
  
  @production(2)
  def pBigIntTimes$1(v0 : BigInt_0_Times, v1 : BigInt_1_Times): BigInt_TOPLEVEL = v0.v * v1.v
  
  @production(1)
  def pBigIntDivision$1(v0 : BigInt_0_Division, v1 : BigInt_1_Division): BigInt_TOPLEVEL = v0.v / v1.v
  
  @production(1)
  def pBigIntIfExpr$1(v0 : Boolean_0_IfExpr, v1 : BigInt_1_IfExpr, v2 : BigInt_2_IfExpr): BigInt_TOPLEVEL = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(1)
  def pBigIntRemainder$1(v0 : BigInt_0_Remainder, v1 : BigInt_1_Remainder): BigInt_TOPLEVEL = v0.v % v1.v
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$11(): BigInt_0_Equals = BigInt(2)
  
  @production(2)
  def pBigIntRemainder$2(v0 : BigInt_0_Remainder, v1 : BigInt_1_Remainder): BigInt_0_Equals = v0.v % v1.v
  
  @production(2)
  def pBigIntVariable$2(): BigInt_0_Equals = variable[BigInt]
  
  @production(1)
  def pBigIntPlus$1(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_0_Equals = v0.v + v1.v
  
  @production(5)
  def pBigIntInfiniteIntegerLiteral$12(): BigInt_1_Equals = BigInt(0)
  
  @production(2)
  def pBigIntVariable$3(): BigInt_1_Equals = variable[BigInt]
  
  @production(3)
  def pBigIntInfiniteIntegerLiteral$13(): BigInt_0_LessThan = BigInt(0)
  
  @production(2)
  def pBigIntVariable$4(): BigInt_0_LessThan = variable[BigInt]
  
  @production(5)
  def pBigIntVariable$5(): BigInt_0_Tuple = variable[BigInt]
  
  @production(5)
  def pBigIntVariable$6(): BigInt_1_LessThan = variable[BigInt]
  
  @production(3)
  def pBigIntVariable$7(): BigInt_1_Tuple = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$14(): BigInt_1_Tuple = BigInt(0)
  
  @production(1)
  def pBigIntPlus$2(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_1_Tuple = v0.v + v1.v
  
  @production(2)
  def pBigIntMinus$1(v0 : BigInt_0_Minus, v1 : BigInt_1_Minus): BigInt_0_FunctionInvocation = v0.v - v1.v
  
  @production(2)
  def pBigIntVariable$8(): BigInt_0_FunctionInvocation = variable[BigInt]
  
  @production(4)
  def pBigIntVariable$9(): BigInt_0_Minus = variable[BigInt]
  
  @production(2)
  def pBigIntMinus$2(v0 : BigInt_0_Minus, v1 : BigInt_1_Minus): BigInt_1_FunctionInvocation = v0.v - v1.v
  
  @production(2)
  def pBigIntVariable$10(): BigInt_1_FunctionInvocation = variable[BigInt]
  
  @production(3)
  def pBigIntVariable$11(): BigInt_1_Minus = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$15(): BigInt_1_Minus = BigInt(1)
  
  @production(3)
  def pBigIntVariable$12(): BigInt_0_Remainder = variable[BigInt]
  
  @production(3)
  def pBigIntVariable$13(): BigInt_0_Times = variable[BigInt]
  
  @production(2)
  def pBigIntVariable$14(): BigInt_1_Remainder = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$16(): BigInt_1_Remainder = BigInt(2)
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$17(): BigInt_0_LessEquals = BigInt(0)
  
  @production(1)
  def pBigIntTimes$2(v0 : BigInt_0_Times, v1 : BigInt_1_Times): BigInt_0_Plus = v0.v * v1.v
  
  @production(1)
  def pBigIntVariable$15(): BigInt_0_Plus = variable[BigInt]
  
  @production(1)
  def pBigIntVariable$16(): BigInt_1_IfExpr = variable[BigInt]
  
  @production(2)
  def pBigIntVariable$17(): BigInt_1_LessEquals = variable[BigInt]
  
  @production(1)
  def pBigIntVariable$18(): BigInt_1_Times = variable[BigInt]
  
  @production(1)
  def pBigIntIfExpr$2(v0 : Boolean_0_IfExpr, v1 : BigInt_1_IfExpr, v2 : BigInt_2_IfExpr): BigInt_2_IfExpr = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(1)
  def pBigIntVariable$19(): BigInt_0_Division = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$18(): BigInt_1_Division = BigInt(2)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$19(): BigInt_1_Plus = BigInt(1)
  
  @production(3)
  def pBooleanEquals$1(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_TOPLEVEL = v0.v == v1.v
  
  @production(2)
  def pBooleanAnd$1(v0 : Boolean_0_And, v1 : Boolean_1_And): Boolean_TOPLEVEL = v0.v && v1.v
  
  @production(2)
  def pBooleanNot$1(v0 : Boolean_0_Not): Boolean_TOPLEVEL = !v0.v
  
  @production(1)
  def pBooleanLessEquals$1(v0 : BigInt_0_LessEquals, v1 : BigInt_1_LessEquals): Boolean_TOPLEVEL = v0.v <= v1.v
  
  @production(1)
  def pBooleanLessThan$1(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_TOPLEVEL = v0.v < v1.v
  
  @production(1)
  def pBooleanLessEquals$2(v0 : BigInt_0_LessEquals, v1 : BigInt_1_LessEquals): Boolean_0_And = v0.v <= v1.v
  
  @production(1)
  def pBooleanLessThan$2(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_0_And = v0.v < v1.v
  
  @production(1)
  def pBooleanEquals$2(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_IfExpr = v0.v == v1.v
  
  @production(1)
  def pBooleanLessThan$3(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_0_IfExpr = v0.v < v1.v
  
  @production(2)
  def pBooleanEquals$3(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_Not = v0.v == v1.v
  
  @production(2)
  def pBooleanLessThan$4(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_1_And = v0.v < v1.v
  
  @production(1)
  def pBooleanEquals$4(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_Lambda = v0.v == v1.v
  
  @production(1)
  def fd$0(v0 : BigInt_0_FunctionInvocation, v1 : BigInt_1_FunctionInvocation): BigInt_1_IfExpr = gcd(v0.v, v1.v)
  
  @production(1)
  def fd$1(v0 : BigInt_0_FunctionInvocation, v1 : BigInt_1_FunctionInvocation): BigInt_1_Times = power(v0.v, v1.v)
  
  @production(1)
  def fd$2(v0 : BigInt_0_FunctionInvocation, v1 : BigInt_1_FunctionInvocation): BigInt_2_IfExpr = gcd(v0.v, v1.v)
  
  @production(1)
  def pBigIntStart$0(v0 : BigInt_TOPLEVEL): BigInt = v0.v
  
  @production(1)
  def pBooleanStart$0(v0 : Boolean_TOPLEVEL): Boolean = v0.v
}

