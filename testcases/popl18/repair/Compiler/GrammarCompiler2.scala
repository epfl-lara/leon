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
import compiler.Trees
import Trees.Expr
import compiler.Desugar._
import compiler.Semantics._
import compiler.Evaluator._

object GrammarCompiler {
  @label
  implicit class BigInt_2_IfExpr(val v : BigInt)
  
  @label
  implicit class BigInt_1_IfExpr(val v : BigInt)
  
  @label
  implicit class BigInt_1_Equals(val v : BigInt)
  
  @label
  implicit class BigInt_0_Equals(val v : BigInt)
  
  @label
  implicit class BigInt_0_FunctionInvocation(val v : BigInt)
  
  @label
  implicit class BigInt_0_CaseClass(val v : BigInt)
  
  @label
  implicit class BigInt_0_Minus(val v : BigInt)
  
  @label
  implicit class BigInt_0_UMinus(val v : BigInt)
  
  @label
  implicit class BigInt_1_LessThan(val v : BigInt)
  
  @label
  implicit class BigInt_1_Plus(val v : BigInt)
  
  @label
  implicit class BigInt_TOPLEVEL(val v : BigInt)
  
  @label
  implicit class BigInt_1_Minus(val v : BigInt)
  
  @label
  implicit class BigInt_0_Plus(val v : BigInt)
  
  @label
  implicit class BigInt_0_LessThan(val v : BigInt)
  
  @label
  implicit class Expr$0_0_FunctionInvocation(val v : Expr)
  
  @label
  implicit class Expr$0_TOPLEVEL(val v : Expr)
  
  @label
  implicit class Expr$0_0_CaseClass(val v : Expr)
  
  @label
  implicit class Boolean_2_IfExpr(val v : Boolean)
  
  @label
  implicit class Boolean_1_IfExpr(val v : Boolean)
  
  @label
  implicit class Boolean_1_And(val v : Boolean)
  
  @label
  implicit class Boolean_1_Equals(val v : Boolean)
  
  @label
  implicit class Boolean_1_Or(val v : Boolean)
  
  @label
  implicit class Boolean_0_IfExpr(val v : Boolean)
  
  @label
  implicit class Boolean_0_Equals(val v : Boolean)
  
  @label
  implicit class Boolean_0_FunctionInvocation(val v : Boolean)
  
  @label
  implicit class Boolean_0_CaseClass(val v : Boolean)
  
  @label
  implicit class Boolean_0_Not(val v : Boolean)
  
  @label
  implicit class Boolean_0_Or(val v : Boolean)
  
  @label
  implicit class Boolean_TOPLEVEL(val v : Boolean)
  
  @label
  implicit class Boolean_0_Lambda(val v : Boolean)
  
  @label
  implicit class Boolean_0_And(val v : Boolean)
  
  @label
  implicit class SimpleE$0_0_FunctionInvocation(val v : SimpleE)
  
  @label
  implicit class SimpleE$0_0_CaseClass(val v : SimpleE)
  
  @label
  implicit class SimpleE$0_2_CaseClass(val v : SimpleE)
  
  @label
  implicit class SimpleE$0_TOPLEVEL(val v : SimpleE)
  
  @label
  implicit class SimpleE$0_1_CaseClass(val v : SimpleE)
  
  @production(8)
  def pBigIntIfExpr$1(v0 : Boolean_0_IfExpr, v1 : BigInt_1_IfExpr, v2 : BigInt_2_IfExpr): BigInt_TOPLEVEL = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(5)
  def pBigIntPlus$1(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_TOPLEVEL = v0.v + v1.v
  
  @production(4)
  def pBigIntVariable$1(): BigInt_TOPLEVEL = variable[BigInt]
  
  @production(2)
  def pBigIntMinus$1(v0 : BigInt_0_Minus, v1 : BigInt_1_Minus): BigInt_TOPLEVEL = v0.v - v1.v
  
  @production(1)
  def pBigIntUMinus$1(v0 : BigInt_0_UMinus): BigInt_TOPLEVEL = -v0.v
  
  @production(3)
  def pBigIntVariable$2(): BigInt_0_Equals = variable[BigInt]
  
  @production(5)
  def pBigIntInfiniteIntegerLiteral$2(): BigInt_1_Equals = BigInt(0)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$3(): BigInt_1_Equals = BigInt(1)
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$4(): BigInt_1_IfExpr = BigInt(1)
  
  @production(3)
  def pBigIntInfiniteIntegerLiteral$5(): BigInt_2_IfExpr = BigInt(0)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$6(): BigInt_2_IfExpr = BigInt(1)
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$7(): BigInt_0_CaseClass = BigInt(1)
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$8(): BigInt_0_CaseClass = BigInt(0)
  
  @production(1)
  def pBigIntPlus$2(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_0_CaseClass = v0.v + v1.v
  
  @production(1)
  def pBigIntVariable$3(): BigInt_0_CaseClass = variable[BigInt]
  
  @production(1)
  def pBigIntVariable$4(): BigInt_0_Plus = variable[BigInt]
  
  @production(1)
  def pBigIntVariable$5(): BigInt_1_Plus = variable[BigInt]
  
  @production(74)
  def pExpr$0Variable$1(): Expr$0_0_FunctionInvocation = variable[Expr]
  
  @production(30)
  def pExpr$0Variable$2(): Expr$0_TOPLEVEL = variable[Expr]
  
  @production(1)
  def pExpr$0Not0$0(v0 : Expr$0_0_CaseClass): Expr$0_TOPLEVEL = Trees.Not(v0.v)
  
  @production(2)
  def pExpr$0BoolLiteral0$0(v0 : Boolean_0_CaseClass): Expr$0_TOPLEVEL = Trees.BoolLiteral(v0.v)
  
  @production(1)
  def pExpr$0IntLiteral0$0(v0 : BigInt_0_CaseClass): Expr$0_TOPLEVEL = Trees.IntLiteral(v0.v)
  
  @production(1)
  def pExpr$0Variable$3(): Expr$0_0_CaseClass = variable[Expr]
  
  @production(4)
  def pBooleanEquals$2(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_FunctionInvocation = v0.v == v1.v
  
  @production(3)
  def pBooleanLessThan$1(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_0_FunctionInvocation = v0.v < v1.v
  
  @production(3)
  def pBooleanVariable$1(): Boolean_0_FunctionInvocation = variable[Boolean]
  
  @production(1)
  def pBooleanAnd$1(v0 : Boolean_0_And, v1 : Boolean_1_And): Boolean_0_FunctionInvocation = v0.v && v1.v
  
  @production(1)
  def pBooleanNot$1(v0 : Boolean_0_Not): Boolean_0_FunctionInvocation = !v0.v
  
  @production(1)
  def pBooleanOr$1(v0 : Boolean_0_Or, v1 : Boolean_1_Or): Boolean_0_FunctionInvocation = v0.v || v1.v
  
  @production(4)
  def pBooleanEquals$3(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_TOPLEVEL = v0.v == v1.v
  
  @production(1)
  def pBooleanEquals$4(v0 : Boolean_0_Equals, v1 : Boolean_1_Equals): Boolean_TOPLEVEL = v0.v == v1.v
  
  @production(1)
  def pBooleanAnd$2(v0 : Boolean_0_And, v1 : Boolean_1_And): Boolean_TOPLEVEL = v0.v && v1.v
  
  @production(1)
  def pBooleanBooleanLiteral$2(): Boolean_TOPLEVEL = true
  
  @production(1)
  def pBooleanIfExpr$1(v0 : Boolean_0_IfExpr, v1 : Boolean_1_IfExpr, v2 : Boolean_2_IfExpr): Boolean_TOPLEVEL = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(1)
  def pBooleanLessThan$2(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_TOPLEVEL = v0.v < v1.v
  
  @production(1)
  def pBooleanNot$2(v0 : Boolean_0_Not): Boolean_TOPLEVEL = !v0.v
  
  @production(1)
  def pBooleanOr$2(v0 : Boolean_0_Or, v1 : Boolean_1_Or): Boolean_TOPLEVEL = v0.v || v1.v
  
  @production(1)
  def pBooleanVariable$2(): Boolean_TOPLEVEL = variable[Boolean]
  
  @production(2)
  def pBooleanEquals$5(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_IfExpr = v0.v == v1.v
  
  @production(2)
  def pBooleanNot$3(v0 : Boolean_0_Not): Boolean_0_IfExpr = !v0.v
  
  @production(2)
  def pBooleanVariable$3(): Boolean_0_IfExpr = variable[Boolean]
  
  @production(2)
  def pBooleanEquals$6(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_Not = v0.v == v1.v
  
  @production(1)
  def pBooleanBooleanLiteral$3(): Boolean_0_CaseClass = false
  
  @production(1)
  def pBooleanBooleanLiteral$4(): Boolean_0_CaseClass = true
  
  @production(2)
  def pBooleanEquals$7(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_Lambda = v0.v == v1.v
  
  @production(2)
  def pSimpleE$0Literal0$0(v0 : BigInt_0_CaseClass): SimpleE$0_TOPLEVEL = Literal(v0.v)
  
  @production(4)
  def pSimpleE$0Ite0$0(v0 : SimpleE$0_0_CaseClass, v1 : SimpleE$0_1_CaseClass, v2 : SimpleE$0_2_CaseClass): SimpleE$0_TOPLEVEL = Ite(v0.v, v1.v, v2.v)
  
  @production(1)
  def pSimpleE$0Eq0$0(v0 : SimpleE$0_0_CaseClass, v1 : SimpleE$0_1_CaseClass): SimpleE$0_TOPLEVEL = Eq(v0.v, v1.v)
  
  @production(2)
  def pSimpleE$0Plus0$0(v0 : SimpleE$0_0_CaseClass, v1 : SimpleE$0_1_CaseClass): SimpleE$0_TOPLEVEL = Plus(v0.v, v1.v)
  
  @production(1)
  def pSimpleE$0LessThan0$0(v0 : SimpleE$0_0_CaseClass, v1 : SimpleE$0_1_CaseClass): SimpleE$0_TOPLEVEL = LessThan(v0.v, v1.v)
  
  @production(1)
  def pSimpleE$0Variable$1(): SimpleE$0_TOPLEVEL = variable[SimpleE]
  
  @production(11)
  def pSimpleE$0Variable$2(): SimpleE$0_0_FunctionInvocation = variable[SimpleE]
  
  @production(1)
  def pSimpleE$0Neg0$0(v0 : SimpleE$0_0_CaseClass): SimpleE$0_1_CaseClass = Neg(v0.v)
  
  @production(2)
  def pSimpleE$0Literal0$1(v0 : BigInt_0_CaseClass): SimpleE$0_1_CaseClass = Literal(v0.v)
  
  @production(2)
  def pSimpleE$0Literal0$2(v0 : BigInt_0_CaseClass): SimpleE$0_2_CaseClass = Literal(v0.v)
  
  @production(6)
  def fd$0(v0 : Boolean_0_FunctionInvocation): BigInt_TOPLEVEL = b2i(v0.v)
  
  @production(6)
  def fd$1(v0 : Boolean_0_FunctionInvocation): BigInt_TOPLEVEL = bToi(v0.v)
  
  @production(5)
  def fd$2(v0 : Expr$0_0_FunctionInvocation): BigInt_0_Equals = semUntyped(v0.v)
  
  @production(3)
  def fd$3(v0 : SimpleE$0_0_FunctionInvocation): BigInt_0_Equals = sem(v0.v)
  
  @production(2)
  def fd$4(v0 : Expr$0_0_FunctionInvocation): BigInt_0_Equals = eval(v0.v)
  
  @production(1)
  def fd$5(v0 : Expr$0_0_FunctionInvocation): BigInt_0_Equals = semI(v0.v)
  
  @production(2)
  def fd$6(v0 : Expr$0_0_FunctionInvocation): BigInt_1_Equals = semUntyped(v0.v)
  
  @production(2)
  def fd$7(v0 : Expr$0_0_FunctionInvocation): BigInt_1_Equals = eval(v0.v)
  
  @production(2)
  def fd$8(v0 : Expr$0_0_FunctionInvocation): BigInt_1_Equals = semI(v0.v)
  
  @production(1)
  def fd$9(v0 : Boolean_0_FunctionInvocation): BigInt_1_Equals = b2i(v0.v)
  
  @production(1)
  def fd$10(v0 : SimpleE$0_0_FunctionInvocation): BigInt_1_Equals = sem(v0.v)
  
  @production(6)
  def fd$11(v0 : Expr$0_0_FunctionInvocation): BigInt_0_FunctionInvocation = eval(v0.v)
  
  @production(3)
  def fd$12(v0 : Expr$0_0_FunctionInvocation): BigInt_1_IfExpr = semUntyped(v0.v)
  
  @production(1)
  def fd$13(v0 : SimpleE$0_0_FunctionInvocation): BigInt_1_IfExpr = sem(v0.v)
  
  @production(1)
  def fd$14(v0 : Expr$0_0_FunctionInvocation): BigInt_1_IfExpr = eval(v0.v)
  
  @production(1)
  def fd$15(v0 : Expr$0_0_FunctionInvocation): BigInt_1_IfExpr = semI(v0.v)
  
  @production(2)
  def fd$16(v0 : Expr$0_0_FunctionInvocation): BigInt_0_Plus = eval(v0.v)
  
  @production(1)
  def fd$17(v0 : Expr$0_0_FunctionInvocation): BigInt_0_Plus = semUntyped(v0.v)
  
  @production(1)
  def fd$18(v0 : SimpleE$0_0_FunctionInvocation): BigInt_0_Plus = sem(v0.v)
  
  @production(1)
  def fd$19(v0 : Expr$0_0_FunctionInvocation): BigInt_0_Plus = semI(v0.v)
  
  @production(2)
  def fd$20(v0 : Expr$0_0_FunctionInvocation): BigInt_1_Plus = eval(v0.v)
  
  @production(1)
  def fd$21(v0 : Expr$0_0_FunctionInvocation): BigInt_1_Plus = semUntyped(v0.v)
  
  @production(1)
  def fd$22(v0 : SimpleE$0_0_FunctionInvocation): BigInt_1_Plus = sem(v0.v)
  
  @production(1)
  def fd$23(v0 : Expr$0_0_FunctionInvocation): BigInt_1_Plus = semI(v0.v)
  
  @production(1)
  def fd$24(v0 : Expr$0_0_FunctionInvocation): BigInt_0_LessThan = semUntyped(v0.v)
  
  @production(1)
  def fd$25(v0 : SimpleE$0_0_FunctionInvocation): BigInt_0_LessThan = sem(v0.v)
  
  @production(1)
  def fd$26(v0 : Expr$0_0_FunctionInvocation): BigInt_0_LessThan = eval(v0.v)
  
  @production(1)
  def fd$27(v0 : Expr$0_0_FunctionInvocation): BigInt_0_LessThan = semI(v0.v)
  
  @production(1)
  def fd$28(v0 : Expr$0_0_FunctionInvocation): BigInt_1_LessThan = semUntyped(v0.v)
  
  @production(1)
  def fd$29(v0 : SimpleE$0_0_FunctionInvocation): BigInt_1_LessThan = sem(v0.v)
  
  @production(1)
  def fd$30(v0 : Expr$0_0_FunctionInvocation): BigInt_1_LessThan = eval(v0.v)
  
  @production(1)
  def fd$31(v0 : Expr$0_0_FunctionInvocation): BigInt_1_LessThan = semI(v0.v)
  
  @production(1)
  def fd$32(v0 : Expr$0_0_FunctionInvocation): BigInt_2_IfExpr = semUntyped(v0.v)
  
  @production(1)
  def fd$33(v0 : SimpleE$0_0_FunctionInvocation): BigInt_2_IfExpr = sem(v0.v)
  
  @production(1)
  def fd$34(v0 : Expr$0_0_FunctionInvocation): BigInt_2_IfExpr = eval(v0.v)
  
  @production(1)
  def fd$35(v0 : Expr$0_0_FunctionInvocation): BigInt_2_IfExpr = semI(v0.v)
  
  @production(1)
  def fd$36(v0 : Expr$0_0_FunctionInvocation): BigInt_0_Minus = semUntyped(v0.v)
  
  @production(1)
  def fd$37(v0 : Expr$0_0_FunctionInvocation): BigInt_0_Minus = semI(v0.v)
  
  @production(1)
  def fd$38(v0 : Expr$0_0_FunctionInvocation): BigInt_1_Minus = semUntyped(v0.v)
  
  @production(1)
  def fd$39(v0 : Expr$0_0_FunctionInvocation): BigInt_1_Minus = semI(v0.v)
  
  @production(1)
  def fd$40(v0 : Boolean_0_FunctionInvocation): BigInt_0_CaseClass = b2i(v0.v)
  
  @production(1)
  def fd$41(v0 : SimpleE$0_0_FunctionInvocation): BigInt_0_UMinus = sem(v0.v)
  
  @production(2)
  def fd$42(v0 : Expr$0_0_FunctionInvocation): Boolean_0_IfExpr = semB(v0.v)
  
  @production(1)
  def fd$43(v0 : BigInt_0_FunctionInvocation): Boolean_0_IfExpr = iTob(v0.v)
  
  @production(1)
  def fd$44(v0 : BigInt_0_FunctionInvocation): Boolean_0_And = iTob(v0.v)
  
  @production(1)
  def fd$45(v0 : Expr$0_0_FunctionInvocation): Boolean_0_And = semB(v0.v)
  
  @production(1)
  def fd$46(v0 : BigInt_0_FunctionInvocation): Boolean_0_Not = iTob(v0.v)
  
  @production(1)
  def fd$47(v0 : Expr$0_0_FunctionInvocation): Boolean_0_Not = semB(v0.v)
  
  @production(1)
  def fd$48(v0 : BigInt_0_FunctionInvocation): Boolean_0_Or = iTob(v0.v)
  
  @production(1)
  def fd$49(v0 : Expr$0_0_FunctionInvocation): Boolean_0_Or = semB(v0.v)
  
  @production(1)
  def fd$50(v0 : BigInt_0_FunctionInvocation): Boolean_1_And = iTob(v0.v)
  
  @production(1)
  def fd$51(v0 : Expr$0_0_FunctionInvocation): Boolean_1_And = semB(v0.v)
  
  @production(1)
  def fd$52(v0 : BigInt_0_FunctionInvocation): Boolean_1_Or = iTob(v0.v)
  
  @production(1)
  def fd$53(v0 : Expr$0_0_FunctionInvocation): Boolean_1_Or = semB(v0.v)
  
  @production(1)
  def fd$54(v0 : Expr$0_0_FunctionInvocation): Boolean_0_Equals = semB(v0.v)
  
  @production(1)
  def fd$55(v0 : Expr$0_0_FunctionInvocation): Boolean_0_FunctionInvocation = semB(v0.v)
  
  @production(1)
  def fd$56(v0 : Expr$0_0_FunctionInvocation): Boolean_1_Equals = semB(v0.v)
  
  @production(1)
  def fd$57(v0 : Expr$0_0_FunctionInvocation): Boolean_1_IfExpr = semB(v0.v)
  
  @production(1)
  def fd$58(v0 : Expr$0_0_FunctionInvocation): Boolean_2_IfExpr = semB(v0.v)
  
  @production(9)
  def fd$59(v0 : Expr$0_0_FunctionInvocation): SimpleE$0_0_CaseClass = desugar(v0.v)
  
  @production(5)
  def fd$60(v0 : Expr$0_0_FunctionInvocation): SimpleE$0_1_CaseClass = desugar(v0.v)
  
  @production(2)
  def fd$61(v0 : Expr$0_0_FunctionInvocation): SimpleE$0_2_CaseClass = desugar(v0.v)
  
  @production(1)
  def pExpr$0Start$0(v0 : Expr$0_TOPLEVEL): Expr = v0.v
  
  @production(1)
  def pSimpleE$0Start$0(v0 : SimpleE$0_TOPLEVEL): SimpleE = v0.v
  
  @production(1)
  def pBigIntStart$0(v0 : BigInt_TOPLEVEL): BigInt = v0.v
  
  @production(1)
  def pBooleanStart$0(v0 : Boolean_TOPLEVEL): Boolean = v0.v
}

