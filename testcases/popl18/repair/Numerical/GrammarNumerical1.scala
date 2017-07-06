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
  @production(47)
  @tag("top")
  def pBigIntVariable(): BigInt = variable[BigInt]
  
  @production(12)
  @tag("0")
  def pBigIntInfiniteIntegerLiteral$0(): BigInt = BigInt(0)
  
  @production(4)
  @tag("1")
  def pBigIntInfiniteIntegerLiteral$1(): BigInt = BigInt(1)
  
  @production(4)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$2(): BigInt = BigInt(2)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$3(): BigInt = BigInt(1024)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$4(): BigInt = BigInt(128)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$5(): BigInt = BigInt(12)
  
  @production(4)
  @tag("minus")
  def pBigIntMinus(v0 : BigInt, v1 : BigInt): BigInt = v0 - v1
  
  @production(3)
  @tag("top")
  def pBigIntRemainder(v0 : BigInt, v1 : BigInt): BigInt = v0 % v1
  
  @production(3)
  @tag("times")
  def pBigIntTimes(v0 : BigInt, v1 : BigInt): BigInt = v0 * v1
  
  @production(2)
  @tag("ite")
  def pBigIntIfExpr(v0 : Boolean, v1 : BigInt, v2 : BigInt): BigInt = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(2)
  @tag("plus")
  def pBigIntPlus(v0 : BigInt, v1 : BigInt): BigInt = v0 + v1
  
  @production(1)
  @tag("div")
  def pBigIntDivision(v0 : BigInt, v1 : BigInt): BigInt = v0 / v1
  
  @production(7)
  @tag("equals")
  def pBooleanEquals(v0 : BigInt, v1 : BigInt): Boolean = v0 == v1
  
  @production(5)
  @tag("top")
  def pBooleanLessThan(v0 : BigInt, v1 : BigInt): Boolean = v0 < v1
  
  @production(2)
  @tag("and")
  def pBooleanAnd(v0 : Boolean, v1 : Boolean): Boolean = v0 && v1
  
  @production(2)
  @tag("top")
  def pBooleanLessEquals(v0 : BigInt, v1 : BigInt): Boolean = v0 <= v1
  
  @production(2)
  @tag("not")
  def pBooleanNot(v0 : Boolean): Boolean = !v0
}

