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
import compiler.Desugar._
import compiler.Trees
import Trees.Expr

object GrammarCompiler {
  @production(10)
  @tag("0")
  def pBigIntInfiniteIntegerLiteral$0(): BigInt = BigInt(0)
  
  @production(6)
  @tag("1")
  def pBigIntInfiniteIntegerLiteral$1(): BigInt = BigInt(1)
  
  @production(10)
  @tag("top")
  def pBigIntVariable(): BigInt = variable[BigInt]
  
  @production(8)
  @tag("ite")
  def pBigIntIfExpr(v0 : Boolean, v1 : BigInt, v2 : BigInt): BigInt = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(6)
  @tag("plus")
  def pBigIntPlus(v0 : BigInt, v1 : BigInt): BigInt = v0 + v1
  
  @production(2)
  @tag("minus")
  def pBigIntMinus(v0 : BigInt, v1 : BigInt): BigInt = v0 - v1
  
  @production(1)
  @tag("top")
  def pBigIntUMinus(v0 : BigInt): BigInt = -v0
  
  @production(105)
  @tag("top")
  def pExpr$0Variable(): Expr = variable[Expr]
  
  @production(1)
  @tag("top")
  def pExpr$0Not(e : Expr): Expr = Trees.Not(e)
  
  @production(2)
  @tag("top")
  def pExpr$0BoolLiteral(b : Boolean): Expr = Trees.BoolLiteral(b)
  
  @production(1)
  @tag("top")
  def pExpr$0IntLiteral(v : BigInt): Expr = Trees.IntLiteral(v)
  
  @production(14)
  @tag("equals")
  def pBooleanEquals(v0 : BigInt, v1 : BigInt): Boolean = v0 == v1
  
  @production(1)
  @tag("equals")
  def pBooleanEquals(v0 : Boolean, v1 : Boolean): Boolean = v0 == v1
  
  @production(6)
  @tag("top")
  def pBooleanVariable(): Boolean = variable[Boolean]
  
  @production(4)
  @tag("top")
  def pBooleanLessThan(v0 : BigInt, v1 : BigInt): Boolean = v0 < v1
  
  @production(4)
  @tag("not")
  def pBooleanNot(v0 : Boolean): Boolean = !v0
  
  @production(2)
  @tag("booleanC")
  def pBooleanBooleanLiteral$0(): Boolean = true
  
  @production(1)
  @tag("booleanC")
  def pBooleanBooleanLiteral$1(): Boolean = false
  
  @production(2)
  @tag("and")
  def pBooleanAnd(v0 : Boolean, v1 : Boolean): Boolean = v0 && v1
  
  @production(2)
  @tag("or")
  def pBooleanOr(v0 : Boolean, v1 : Boolean): Boolean = v0 || v1
  
  @production(1)
  @tag("ite")
  def pBooleanIfExpr(v0 : Boolean, v1 : Boolean, v2 : Boolean): Boolean = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(1)
  @tag("top")
  def pSimpleE$0Neg(arg : SimpleE): SimpleE = Neg(arg)
  
  @production(6)
  @tag("top")
  def pSimpleE$0Literal(i : BigInt): SimpleE = Literal(i)
  
  @production(4)
  @tag("top")
  def pSimpleE$0Ite(cond : SimpleE, thn : SimpleE, els : SimpleE): SimpleE = Ite(cond, thn, els)
  
  @production(1)
  @tag("top")
  def pSimpleE$0Eq(lhs : SimpleE, rhs : SimpleE): SimpleE = Eq(lhs, rhs)
  
  @production(2)
  @tag("top")
  def pSimpleE$0Plus(lhs : SimpleE, rhs : SimpleE): SimpleE = Plus(lhs, rhs)
  
  @production(1)
  @tag("top")
  def pSimpleE$0LessThan(lhs : SimpleE, rhs : SimpleE): SimpleE = LessThan(lhs, rhs)
  
  @production(12)
  @tag("top")
  def pSimpleE$0Variable(): SimpleE = variable[SimpleE]
}

