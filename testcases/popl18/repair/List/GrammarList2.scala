package leon
package grammar
import leon.custom._
import leon.custom.List._
import leon.custom.ListOps._
import leon.custom.ListSpecs._
import leon.lang.Set._
import leon.lang._
import leon.lang._
import leon.lang.synthesis._
import leon.math._
import annotation.grammar._

object GrammarList {
  @label
  implicit class TP$0_List_1_Tuple[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_1_IfExpr[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_1_CaseClass[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_2_IfExpr[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_TOPLEVEL[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_0_Tuple[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_0_Equals[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_1_Equals[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_1_FunctionInvocation[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_0_FunctionInvocation[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_List_2_FunctionInvocation[TP$0](val v : List[TP$0])
  
  @label
  implicit class TP$0_Set_1_SetUnion[TP$0](val v : Set[TP$0])
  
  @label
  implicit class TP$0_Set_1_ElementOfSet[TP$0](val v : Set[TP$0])
  
  @label
  implicit class TP$0_Set_0_SetUnion[TP$0](val v : Set[TP$0])
  
  @label
  implicit class TP$0_Set_TOPLEVEL[TP$0](val v : Set[TP$0])
  
  @label
  implicit class TP$0_Set_0_Equals[TP$0](val v : Set[TP$0])
  
  @label
  implicit class TP$0_Set_1_Equals[TP$0](val v : Set[TP$0])
  
  @label
  implicit class BigInt_1_Tuple(val v : BigInt)
  
  @label
  implicit class BigInt_0_Plus(val v : BigInt)
  
  @label
  implicit class BigInt_1_LessEquals(val v : BigInt)
  
  @label
  implicit class BigInt_1_IfExpr(val v : BigInt)
  
  @label
  implicit class BigInt_0_Minus(val v : BigInt)
  
  @label
  implicit class BigInt_1_Remainder(val v : BigInt)
  
  @label
  implicit class BigInt_2_IfExpr(val v : BigInt)
  
  @label
  implicit class BigInt_1_LessThan(val v : BigInt)
  
  @label
  implicit class BigInt_1_Minus(val v : BigInt)
  
  @label
  implicit class BigInt_0_LessEquals(val v : BigInt)
  
  @label
  implicit class BigInt_0_Remainder(val v : BigInt)
  
  @label
  implicit class BigInt_TOPLEVEL(val v : BigInt)
  
  @label
  implicit class BigInt_0_LessThan(val v : BigInt)
  
  @label
  implicit class BigInt_1_Division(val v : BigInt)
  
  @label
  implicit class BigInt_1_Plus(val v : BigInt)
  
  @label
  implicit class BigInt_0_Equals(val v : BigInt)
  
  @label
  implicit class BigInt_1_Equals(val v : BigInt)
  
  @label
  implicit class BigInt_1_FunctionInvocation(val v : BigInt)
  
  @label
  implicit class BigInt_2_FunctionInvocation(val v : BigInt)
  
  @label
  implicit class BigInt_0_Division(val v : BigInt)
  
  @label
  implicit class BigInt_0_CaseClass(val v : BigInt)
  
  @label
  implicit class BigInt_Option_TOPLEVEL(val v : Option[BigInt])
  
  @label
  implicit class TP$0_1_Tuple[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_1_IfExpr[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_0_FiniteSet[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_2_IfExpr[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_TOPLEVEL[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_0_Tuple[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_0_Equals[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_1_Equals[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_1_FunctionInvocation[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_2_FunctionInvocation[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_2_Tuple[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_0_ElementOfSet[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_0_CaseClass[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_Option_TOPLEVEL[TP$0](val v : Option[TP$0])
  
  @label
  implicit class TP$0_Option_0_FunctionInvocation[TP$0](val v : Option[TP$0])
  
  @label
  implicit class TP$0_Option_0_Lambda[TP$0](val v : Option[TP$0])
  
  @label
  implicit class BigInt_List_1_IfExpr(val v : List[BigInt])
  
  @label
  implicit class BigInt_List_1_CaseClass(val v : List[BigInt])
  
  @label
  implicit class BigInt_List_2_IfExpr(val v : List[BigInt])
  
  @label
  implicit class BigInt_List_TOPLEVEL(val v : List[BigInt])
  
  @label
  implicit class BigInt_List_0_FunctionInvocation(val v : List[BigInt])
  
  @label
  implicit class Boolean_0_And(val v : Boolean)
  
  @label
  implicit class Boolean_1_IfExpr(val v : Boolean)
  
  @label
  implicit class Boolean_2_IfExpr(val v : Boolean)
  
  @label
  implicit class Boolean_1_And(val v : Boolean)
  
  @label
  implicit class Boolean_0_Or(val v : Boolean)
  
  @label
  implicit class Boolean_TOPLEVEL(val v : Boolean)
  
  @label
  implicit class Boolean_0_IfExpr(val v : Boolean)
  
  @label
  implicit class Boolean_0_Equals(val v : Boolean)
  
  @label
  implicit class Boolean_1_Equals(val v : Boolean)
  
  @label
  implicit class Boolean_0_Lambda(val v : Boolean)
  
  @label
  implicit class Boolean_1_Or(val v : Boolean)
  
  @label
  implicit class Boolean_0_Not(val v : Boolean)
  
  @production(106)
  def pTP$0_ListVariable$1[TP$0](): TP$0_List_0_FunctionInvocation[TP$0] = variable[List[TP$0]]
  
  @production(1)
  def pTP$0_ListNil0$0[TP$0](): TP$0_List_0_FunctionInvocation[TP$0] = Nil[TP$0]()
  
  @production(53)
  def pTP$0_ListVariable$2[TP$0](): TP$0_List_TOPLEVEL[TP$0] = variable[List[TP$0]]
  
  @production(13)
  def pTP$0_ListCons0$0[TP$0](v0 : TP$0_0_CaseClass[TP$0], v1 : TP$0_List_1_CaseClass[TP$0]): TP$0_List_TOPLEVEL[TP$0] = Cons[TP$0](v0.v, v1.v)
  
  @production(14)
  def pTP$0_ListNil0$1[TP$0](): TP$0_List_TOPLEVEL[TP$0] = Nil[TP$0]()
  
  @production(6)
  def pTP$0_ListIfExpr$1[TP$0](v0 : Boolean_0_IfExpr, v1 : TP$0_List_1_IfExpr[TP$0], v2 : TP$0_List_2_IfExpr[TP$0]): TP$0_List_TOPLEVEL[TP$0] = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(2)
  def pTP$0_ListCons0$1[TP$0](v0 : TP$0_0_CaseClass[TP$0], v1 : TP$0_List_1_CaseClass[TP$0]): TP$0_List_1_CaseClass[TP$0] = Cons[TP$0](v0.v, v1.v)
  
  @production(3)
  def pTP$0_ListNil0$2[TP$0](): TP$0_List_1_CaseClass[TP$0] = Nil[TP$0]()
  
  @production(5)
  def pTP$0_ListVariable$3[TP$0](): TP$0_List_1_CaseClass[TP$0] = variable[List[TP$0]]
  
  @production(14)
  def pTP$0_ListVariable$4[TP$0](): TP$0_List_1_FunctionInvocation[TP$0] = variable[List[TP$0]]
  
  @production(1)
  def pTP$0_ListCons0$2[TP$0](v0 : TP$0_0_CaseClass[TP$0], v1 : TP$0_List_1_CaseClass[TP$0]): TP$0_List_1_FunctionInvocation[TP$0] = Cons[TP$0](v0.v, v1.v)
  
  @production(2)
  def pTP$0_ListVariable$5[TP$0](): TP$0_List_0_Equals[TP$0] = variable[List[TP$0]]
  
  @production(1)
  def pTP$0_ListCons0$3[TP$0](v0 : TP$0_0_CaseClass[TP$0], v1 : TP$0_List_1_CaseClass[TP$0]): TP$0_List_1_Equals[TP$0] = Cons[TP$0](v0.v, v1.v)
  
  @production(2)
  def pTP$0_ListNil0$3[TP$0](): TP$0_List_1_Equals[TP$0] = Nil[TP$0]()
  
  @production(1)
  def pTP$0_ListVariable$6[TP$0](): TP$0_List_1_Equals[TP$0] = variable[List[TP$0]]
  
  @production(5)
  def pTP$0_ListVariable$7[TP$0](): TP$0_List_0_Tuple[TP$0] = variable[List[TP$0]]
  
  @production(3)
  def pTP$0_ListCons0$4[TP$0](v0 : TP$0_0_CaseClass[TP$0], v1 : TP$0_List_1_CaseClass[TP$0]): TP$0_List_1_IfExpr[TP$0] = Cons[TP$0](v0.v, v1.v)
  
  @production(1)
  def pTP$0_ListNil0$4[TP$0](): TP$0_List_1_IfExpr[TP$0] = Nil[TP$0]()
  
  @production(4)
  def pTP$0_ListCons0$5[TP$0](v0 : TP$0_0_CaseClass[TP$0], v1 : TP$0_List_1_CaseClass[TP$0]): TP$0_List_2_IfExpr[TP$0] = Cons[TP$0](v0.v, v1.v)
  
  @production(5)
  def pTP$0_ListVariable$8[TP$0](): TP$0_List_2_FunctionInvocation[TP$0] = variable[List[TP$0]]
  
  @production(1)
  def pTP$0_ListVariable$9[TP$0](): TP$0_List_1_Tuple[TP$0] = variable[List[TP$0]]
  
  @production(14)
  def pBigIntVariable$1(): BigInt_1_FunctionInvocation = variable[BigInt]
  
  @production(9)
  def pBigIntMinus$1(v0 : BigInt_0_Minus, v1 : BigInt_1_Minus): BigInt_1_FunctionInvocation = v0.v - v1.v
  
  @production(3)
  def pBigIntPlus$1(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_1_FunctionInvocation = v0.v + v1.v
  
  @production(12)
  def pBigIntVariable$2(): BigInt_0_LessThan = variable[BigInt]
  
  @production(3)
  def pBigIntInfiniteIntegerLiteral$3(): BigInt_0_LessThan = BigInt(0)
  
  @production(4)
  def pBigIntVariable$3(): BigInt_1_LessThan = variable[BigInt]
  
  @production(3)
  def pBigIntInfiniteIntegerLiteral$4(): BigInt_1_LessThan = BigInt(0)
  
  @production(2)
  def pBigIntPlus$2(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_1_LessThan = v0.v + v1.v
  
  @production(7)
  def pBigIntVariable$4(): BigInt_0_Equals = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$5(): BigInt_0_Equals = BigInt(2)
  
  @production(11)
  def pBigIntVariable$5(): BigInt_0_Minus = variable[BigInt]
  
  @production(1)
  def pBigIntMinus$2(v0 : BigInt_0_Minus, v1 : BigInt_1_Minus): BigInt_0_Minus = v0.v - v1.v
  
  @production(10)
  def pBigIntInfiniteIntegerLiteral$6(): BigInt_1_Equals = BigInt(0)
  
  @production(2)
  def pBigIntPlus$3(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_1_Equals = v0.v + v1.v
  
  @production(10)
  def pBigIntInfiniteIntegerLiteral$7(): BigInt_1_Minus = BigInt(1)
  
  @production(2)
  def pBigIntVariable$6(): BigInt_1_Minus = variable[BigInt]
  
  @production(5)
  def pBigIntVariable$7(): BigInt_TOPLEVEL = variable[BigInt]
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$8(): BigInt_TOPLEVEL = BigInt(0)
  
  @production(1)
  def pBigIntDivision$1(v0 : BigInt_0_Division, v1 : BigInt_1_Division): BigInt_TOPLEVEL = v0.v / v1.v
  
  @production(1)
  def pBigIntIfExpr$1(v0 : Boolean_0_IfExpr, v1 : BigInt_1_IfExpr, v2 : BigInt_2_IfExpr): BigInt_TOPLEVEL = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(1)
  def pBigIntMinus$3(v0 : BigInt_0_Minus, v1 : BigInt_1_Minus): BigInt_TOPLEVEL = v0.v - v1.v
  
  @production(1)
  def pBigIntPlus$4(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_TOPLEVEL = v0.v + v1.v
  
  @production(1)
  def pBigIntRemainder$1(v0 : BigInt_0_Remainder, v1 : BigInt_1_Remainder): BigInt_TOPLEVEL = v0.v % v1.v
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$9(): BigInt_0_Plus = BigInt(1)
  
  @production(1)
  def pBigIntVariable$8(): BigInt_0_Plus = variable[BigInt]
  
  @production(3)
  def pBigIntInfiniteIntegerLiteral$10(): BigInt_1_Plus = BigInt(1)
  
  @production(3)
  def pBigIntVariable$9(): BigInt_1_Plus = variable[BigInt]
  
  @production(6)
  def pBigIntInfiniteIntegerLiteral$11(): BigInt_0_LessEquals = BigInt(0)
  
  @production(2)
  def pBigIntVariable$10(): BigInt_0_LessEquals = variable[BigInt]
  
  @production(7)
  def pBigIntVariable$11(): BigInt_1_LessEquals = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$12(): BigInt_1_LessEquals = BigInt(0)
  
  @production(3)
  def pBigIntVariable$12(): BigInt_0_CaseClass = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$13(): BigInt_0_CaseClass = BigInt(0)
  
  @production(1)
  def pBigIntPlus$5(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_0_CaseClass = v0.v + v1.v
  
  @production(4)
  def pBigIntVariable$13(): BigInt_1_Tuple = variable[BigInt]
  
  @production(2)
  def pBigIntMinus$4(v0 : BigInt_0_Minus, v1 : BigInt_1_Minus): BigInt_2_FunctionInvocation = v0.v - v1.v
  
  @production(1)
  def pBigIntVariable$14(): BigInt_2_FunctionInvocation = variable[BigInt]
  
  @production(1)
  def pBigIntVariable$15(): BigInt_0_Remainder = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$14(): BigInt_1_Division = BigInt(2)
  
  @production(1)
  def pBigIntPlus$6(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_1_IfExpr = v0.v + v1.v
  
  @production(12)
  def pBooleanBooleanLiteral$2(): Boolean_TOPLEVEL = true
  
  @production(3)
  def pBooleanBooleanLiteral$3(): Boolean_TOPLEVEL = false
  
  @production(5)
  def pBooleanEquals$5[TP$0](v0 : TP$0_0_Equals[TP$0], v1 : TP$0_1_Equals[TP$0]): Boolean_TOPLEVEL = v0.v == v1.v
  
  @production(3)
  def pBooleanEquals$6(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_TOPLEVEL = v0.v == v1.v
  
  @production(5)
  def pBooleanEquals$7[TP$0](v0 : TP$0_List_0_Equals[TP$0], v1 : TP$0_List_1_Equals[TP$0]): Boolean_TOPLEVEL = v0.v == v1.v
  
  @production(7)
  def pBooleanAnd$1(v0 : Boolean_0_And, v1 : Boolean_1_And): Boolean_TOPLEVEL = v0.v && v1.v
  
  @production(6)
  def pBooleanLessThan$1(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_TOPLEVEL = v0.v < v1.v
  
  @production(4)
  def pBooleanNot$1(v0 : Boolean_0_Not): Boolean_TOPLEVEL = !v0.v
  
  @production(2)
  def pBooleanIfExpr$1(v0 : Boolean_0_IfExpr, v1 : Boolean_1_IfExpr, v2 : Boolean_2_IfExpr): Boolean_TOPLEVEL = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(1)
  def pBooleanLessEquals$1(v0 : BigInt_0_LessEquals, v1 : BigInt_1_LessEquals): Boolean_TOPLEVEL = v0.v <= v1.v
  
  @production(8)
  def pBooleanVariable$1(): Boolean_0_Lambda = variable[Boolean]
  
  @production(3)
  def pBooleanAnd$2(v0 : Boolean_0_And, v1 : Boolean_1_And): Boolean_0_Lambda = v0.v && v1.v
  
  @production(1)
  def pBooleanEquals$8(v0 : Boolean_0_Equals, v1 : Boolean_1_Equals): Boolean_0_Lambda = v0.v == v1.v
  
  @production(1)
  def pBooleanLessEquals$2(v0 : BigInt_0_LessEquals, v1 : BigInt_1_LessEquals): Boolean_0_Lambda = v0.v <= v1.v
  
  @production(1)
  def pBooleanOr$1(v0 : Boolean_0_Or, v1 : Boolean_1_Or): Boolean_0_Lambda = v0.v || v1.v
  
  @production(3)
  def pBooleanEquals$9[TP$0](v0 : TP$0_0_Equals[TP$0], v1 : TP$0_1_Equals[TP$0]): Boolean_0_IfExpr = v0.v == v1.v
  
  @production(4)
  def pBooleanEquals$10(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_IfExpr = v0.v == v1.v
  
  @production(3)
  def pBooleanLessThan$2(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_0_IfExpr = v0.v < v1.v
  
  @production(1)
  def pBooleanLessEquals$3(v0 : BigInt_0_LessEquals, v1 : BigInt_1_LessEquals): Boolean_0_IfExpr = v0.v <= v1.v
  
  @production(4)
  def pBooleanLessEquals$4(v0 : BigInt_0_LessEquals, v1 : BigInt_1_LessEquals): Boolean_0_And = v0.v <= v1.v
  
  @production(1)
  def pBooleanEquals$11[TP$0](v0 : TP$0_Set_0_Equals[TP$0], v1 : TP$0_Set_1_Equals[TP$0]): Boolean_0_And = v0.v == v1.v
  
  @production(2)
  def pBooleanEquals$12(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_And = v0.v == v1.v
  
  @production(2)
  def pBooleanLessThan$3(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_0_And = v0.v < v1.v
  
  @production(4)
  def pBooleanLessThan$4(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_1_And = v0.v < v1.v
  
  @production(2)
  def pBooleanEquals$13[TP$0](v0 : TP$0_Set_0_Equals[TP$0], v1 : TP$0_Set_1_Equals[TP$0]): Boolean_1_And = v0.v == v1.v
  
  @production(1)
  def pBooleanEquals$14(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_1_And = v0.v == v1.v
  
  @production(1)
  def pBooleanAnd$3(v0 : Boolean_0_And, v1 : Boolean_1_And): Boolean_1_And = v0.v && v1.v
  
  @production(1)
  def pBooleanLessEquals$5(v0 : BigInt_0_LessEquals, v1 : BigInt_1_LessEquals): Boolean_1_And = v0.v <= v1.v
  
  @production(2)
  def pBooleanEquals$15(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_0_Not = v0.v == v1.v
  
  @production(2)
  def pBooleanEquals$16[TP$0](v0 : TP$0_List_0_Equals[TP$0], v1 : TP$0_List_1_Equals[TP$0]): Boolean_0_Not = v0.v == v1.v
  
  @production(1)
  def pBooleanBooleanLiteral$4(): Boolean_1_IfExpr = true
  
  @production(1)
  def pBooleanBooleanLiteral$5(): Boolean_2_IfExpr = true
  
  @production(1)
  def pBooleanVariable$2(): Boolean_0_Equals = variable[Boolean]
  
  @production(1)
  def pBooleanLessThan$5(v0 : BigInt_0_LessThan, v1 : BigInt_1_LessThan): Boolean_0_Or = v0.v < v1.v
  
  @production(1)
  def pBooleanElementOfSet$1[TP$0](v0 : TP$0_0_ElementOfSet[TP$0], v1 : TP$0_Set_1_ElementOfSet[TP$0]): Boolean_1_Equals = v1.v.contains(v0.v)
  
  @production(1)
  def pBooleanEquals$17(v0 : BigInt_0_Equals, v1 : BigInt_1_Equals): Boolean_1_Or = v0.v == v1.v
  
  @production(26)
  def pTP$0Variable$1[TP$0](): TP$0_0_CaseClass[TP$0] = variable[TP$0]
  
  @production(24)
  def pTP$0Variable$2[TP$0](): TP$0_1_FunctionInvocation[TP$0] = variable[TP$0]
  
  @production(5)
  def pTP$0Variable$3[TP$0](): TP$0_0_Equals[TP$0] = variable[TP$0]
  
  @production(5)
  def pTP$0Variable$4[TP$0](): TP$0_1_Equals[TP$0] = variable[TP$0]
  
  @production(2)
  def pTP$0IfExpr$1[TP$0](v0 : Boolean_0_IfExpr, v1 : TP$0_1_IfExpr[TP$0], v2 : TP$0_2_IfExpr[TP$0]): TP$0_1_Equals[TP$0] = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(4)
  def pTP$0Variable$5[TP$0](): TP$0_2_FunctionInvocation[TP$0] = variable[TP$0]
  
  @production(1)
  def pTP$0Variable$6[TP$0](): TP$0_2_IfExpr[TP$0] = variable[TP$0]
  
  @production(1)
  def pTP$0IfExpr$2[TP$0](v0 : Boolean_0_IfExpr, v1 : TP$0_1_IfExpr[TP$0], v2 : TP$0_2_IfExpr[TP$0]): TP$0_TOPLEVEL[TP$0] = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(1)
  def pTP$0Variable$7[TP$0](): TP$0_TOPLEVEL[TP$0] = variable[TP$0]
  
  @production(2)
  def pTP$0Variable$8[TP$0](): TP$0_0_FiniteSet[TP$0] = variable[TP$0]
  
  @production(1)
  def pTP$0Variable$9[TP$0](): TP$0_0_ElementOfSet[TP$0] = variable[TP$0]
  
  @production(1)
  def pTP$0Variable$10[TP$0](): TP$0_0_Tuple[TP$0] = variable[TP$0]
  
  @production(1)
  def pTP$0Variable$11[TP$0](): TP$0_1_Tuple[TP$0] = variable[TP$0]
  
  @production(1)
  def pTP$0Variable$12[TP$0](): TP$0_2_Tuple[TP$0] = variable[TP$0]
  
  @production(3)
  def pBigInt_ListVariable$1(): BigInt_List_TOPLEVEL = variable[List[BigInt]]
  
  @production(1)
  def pBigInt_ListCons0$0(v0 : BigInt_0_CaseClass, v1 : BigInt_List_1_CaseClass): BigInt_List_TOPLEVEL = Cons[BigInt](v0.v, v1.v)
  
  @production(1)
  def pBigInt_ListNil0$0(): BigInt_List_TOPLEVEL = Nil[BigInt]()
  
  @production(1)
  def pBigInt_ListIfExpr$1(v0 : Boolean_0_IfExpr, v1 : BigInt_List_1_IfExpr, v2 : BigInt_List_2_IfExpr): BigInt_List_TOPLEVEL = if (v0.v) {
    v1.v
  } else {
    v2.v
  }
  
  @production(3)
  def pBigInt_ListVariable$2(): BigInt_List_0_FunctionInvocation = variable[List[BigInt]]
  
  @production(1)
  def pBigInt_ListNil0$1(): BigInt_List_1_CaseClass = Nil[BigInt]()
  
  @production(1)
  def pBigInt_ListVariable$3(): BigInt_List_1_CaseClass = variable[List[BigInt]]
  
  @production(1)
  def pBigInt_ListCons0$1(v0 : BigInt_0_CaseClass, v1 : BigInt_List_1_CaseClass): BigInt_List_1_IfExpr = Cons[BigInt](v0.v, v1.v)
  
  @production(1)
  def pBigInt_ListCons0$2(v0 : BigInt_0_CaseClass, v1 : BigInt_List_1_CaseClass): BigInt_List_2_IfExpr = Cons[BigInt](v0.v, v1.v)
  
  @production(1)
  def pTP$0_SetFiniteSet$2[TP$0](v0 : TP$0_0_FiniteSet[TP$0]): TP$0_Set_0_SetUnion[TP$0] = Set[TP$0](v0.v)
  
  @production(2)
  def pTP$0_SetSetUnion$1[TP$0](v0 : TP$0_Set_0_SetUnion[TP$0], v1 : TP$0_Set_1_SetUnion[TP$0]): TP$0_Set_1_Equals[TP$0] = v0.v ++ v1.v
  
  @production(1)
  def pTP$0_SetFiniteSet$3[TP$0](v0 : TP$0_0_FiniteSet[TP$0]): TP$0_Set_1_SetUnion[TP$0] = Set[TP$0](v0.v)
  
  @production(1)
  def pTP$0_SetFiniteSet$4[TP$0](): TP$0_Set_TOPLEVEL[TP$0] = Set[TP$0]()
  
  @production(1)
  def pTP$0_SetSetUnion$2[TP$0](v0 : TP$0_Set_0_SetUnion[TP$0], v1 : TP$0_Set_1_SetUnion[TP$0]): TP$0_Set_TOPLEVEL[TP$0] = v0.v ++ v1.v
  
  @production(2)
  def pBigInt_OptionSome0$0(v0 : BigInt_0_CaseClass): BigInt_Option_TOPLEVEL = Some[BigInt](v0.v)
  
  @production(2)
  def pBigInt_OptionNone0$0(): BigInt_Option_TOPLEVEL = None[BigInt]()
  
  @production(1)
  def pTP$0_OptionSome0$0[TP$0](v0 : TP$0_0_CaseClass[TP$0]): TP$0_Option_TOPLEVEL[TP$0] = Some[TP$0](v0.v)
  
  @production(2)
  def pTP$0_OptionNone0$0[TP$0](): TP$0_Option_TOPLEVEL[TP$0] = None[TP$0]()
  
  @production(1)
  def pTP$0_OptionSome0$1[TP$0](v0 : TP$0_0_CaseClass[TP$0]): TP$0_Option_0_Lambda[TP$0] = Some[TP$0](v0.v)
  
  @production(4)
  def fd$35[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_List_0_FunctionInvocation[TP$0] = v0.v.reverse
  
  @production(3)
  def fd$36[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_0_FunctionInvocation[TP$0] = v0.v ++ v1.v
  
  @production(2)
  def fd$37[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_1_FunctionInvocation[TP$0]): TP$0_List_0_FunctionInvocation[TP$0] = v0.v.:+(v1.v)
  
  @production(2)
  def fd$38[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_List_0_FunctionInvocation[TP$0] = v0.v.drop(v1.v)
  
  @production(1)
  def fd$39[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_List_0_FunctionInvocation[TP$0] = v0.v.unique
  
  @production(1)
  def fd$40[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_List_0_FunctionInvocation[TP$0] = v0.v.tail
  
  @production(2)
  def fd$41[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_1_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v - v1.v
  
  @production(2)
  def fd$42[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation, v2 : TP$0_2_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v.pad(v1.v, v2.v)
  
  @production(1)
  def fd$43[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v -- v1.v
  
  @production(1)
  def fd$44[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v.&(v1.v)
  
  @production(1)
  def fd$45[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v.init
  
  @production(1)
  def fd$46[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation, v2 : TP$0_List_2_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v.insertAt(v1.v, v2.v)
  
  @production(1)
  def fd$47[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation, v2 : TP$0_List_2_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v.replaceAt(v1.v, v2.v)
  
  @production(1)
  def fd$48[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v ++ v1.v
  
  @production(1)
  def fd$49[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_1_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v.:+(v1.v)
  
  @production(1)
  def fd$50[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_List_1_CaseClass[TP$0] = v0.v.reverse
  
  @production(1)
  def fd$51[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_List_1_CaseClass[TP$0] = v0.v.take(v1.v)
  
  @production(4)
  def fd$52[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_TOPLEVEL[TP$0] = v0.v ++ v1.v
  
  @production(2)
  def fd$53[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_1_FunctionInvocation[TP$0]): TP$0_List_TOPLEVEL[TP$0] = v0.v.:+(v1.v)
  
  @production(1)
  def fd$54[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation, v2 : TP$0_List_2_FunctionInvocation[TP$0]): TP$0_List_TOPLEVEL[TP$0] = v0.v.insertAt(v1.v, v2.v)
  
  @production(1)
  def fd$55[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation, v2 : TP$0_List_2_FunctionInvocation[TP$0]): TP$0_List_TOPLEVEL[TP$0] = v0.v.replaceAt(v1.v, v2.v)
  
  @production(1)
  def fd$56[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_List_TOPLEVEL[TP$0] = v0.v.rotate(v1.v)
  
  @production(1)
  def fd$57[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_List_TOPLEVEL[TP$0] = v0.v.take(v1.v)
  
  @production(1)
  def fd$58[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_1_FunctionInvocation[TP$0], v2 : TP$0_2_FunctionInvocation[TP$0]): TP$0_List_TOPLEVEL[TP$0] = v0.v.replace(v1.v, v2.v)
  
  @production(2)
  def fd$59[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_1_FunctionInvocation[TP$0]): TP$0_List_0_Equals[TP$0] = v0.v.:+(v1.v)
  
  @production(2)
  def fd$60[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_List_0_Equals[TP$0] = v0.v.reverse
  
  @production(1)
  def fd$61[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_0_Equals[TP$0] = v0.v ++ v1.v
  
  @production(1)
  def fd$62[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_1_FunctionInvocation[TP$0] = v0.v ++ v1.v
  
  @production(1)
  def fd$63[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_1_FunctionInvocation[TP$0]): TP$0_List_1_FunctionInvocation[TP$0] = v0.v.:+(v1.v)
  
  @production(1)
  def fd$64[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_List_1_FunctionInvocation[TP$0] = v0.v.take(v1.v)
  
  @production(1)
  def fd$65[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_List_1_FunctionInvocation[TP$0] = v0.v.drop(v1.v)
  
  @production(3)
  def fd$66[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_1_Equals[TP$0] = v0.v ++ v1.v
  
  @production(1)
  def fd$67[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_1_FunctionInvocation[TP$0]): TP$0_List_1_IfExpr[TP$0] = v0.v - v1.v
  
  @production(1)
  def fd$68[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_1_IfExpr[TP$0] = v0.v -- v1.v
  
  @production(1)
  def fd$69[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : TP$0_List_1_FunctionInvocation[TP$0]): TP$0_List_2_IfExpr[TP$0] = v0.v.&(v1.v)
  
  @production(1)
  def fd$70[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_List_2_IfExpr[TP$0] = v0.v.drop(v1.v)
  
  @production(1)
  def fd$71[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_List_0_Tuple[TP$0] = v0.v.take(v1.v)
  
  @production(1)
  def fd$72[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_List_1_Tuple[TP$0] = v0.v.drop(v1.v)
  
  @production(7)
  def fd$73[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_0_Plus = v0.v.size
  
  @production(7)
  def fd$74[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_1_LessThan = v0.v.size
  
  @production(5)
  def fd$75[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_0_Equals = v0.v.size
  
  @production(3)
  def fd$76[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_1_Plus = v0.v.size
  
  @production(1)
  def fd$77[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T]): BigInt_1_Plus = v0.v.count(v1.v)
  
  @production(1)
  def fd$78[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_0_Division = v0.v.size
  
  @production(1)
  def fd$79[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_0_LessThan = v0.v.size
  
  @production(1)
  def fd$80[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_0_Minus = v0.v.size
  
  @production(1)
  def fd$81[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_1_Equals = v0.v.size
  
  @production(1)
  def fd$82[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_1_FunctionInvocation = v0.v.size
  
  @production(1)
  def fd$83[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_1_Minus = v0.v.size
  
  @production(1)
  def fd$84[T](v0 : TP$0_List_0_FunctionInvocation[T]): BigInt_1_Remainder = v0.v.size
  
  @production(1)
  def fd$85[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T]): BigInt_2_IfExpr = v0.v.count(v1.v)
  
  @production(2)
  def fd$86[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T]): Boolean_TOPLEVEL = v0.v.contains(v1.v)
  
  @production(1)
  def fd$87(v0 : BigInt_List_0_FunctionInvocation): Boolean_TOPLEVEL = isSorted(v0.v)
  
  @production(1)
  def fd$88[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_List_1_FunctionInvocation[T], v2 : TP$0_List_2_FunctionInvocation[T]): Boolean_TOPLEVEL = appendAssoc[T](v0.v, v1.v, v2.v)
  
  @production(1)
  def fd$89[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T]): Boolean_TOPLEVEL = snocIsAppend[T](v0.v, v1.v)
  
  @production(1)
  def fd$90[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_List_1_FunctionInvocation[T], v2 : TP$0_2_FunctionInvocation[T]): Boolean_TOPLEVEL = snocAfterAppend[T](v0.v, v1.v, v2.v)
  
  @production(1)
  def fd$91[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T]): Boolean_TOPLEVEL = snocReverse[T](v0.v, v1.v)
  
  @production(1)
  def fd$92[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T], v2 : BigInt_2_FunctionInvocation): Boolean_0_And = snocIndex[T](v0.v, v1.v, v2.v)
  
  @production(1)
  def fd$93[T](v0 : TP$0_List_0_FunctionInvocation[T]): Boolean_0_And = reverseReverse[T](v0.v)
  
  @production(2)
  def fd$94[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T]): Boolean_0_IfExpr = v0.v.contains(v1.v)
  
  @production(1)
  def fd$95[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : BigInt_1_FunctionInvocation): Boolean_1_And = reverseIndex[T](v0.v, v1.v)
  
  @production(1)
  def fd$96[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T]): Boolean_1_And = snocReverse[T](v0.v, v1.v)
  
  @production(1)
  def fd$97[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T], v2 : BigInt_2_FunctionInvocation): Boolean_1_IfExpr = snocIndex[T](v0.v, v1.v, v2.v)
  
  @production(1)
  def fd$98[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_List_1_FunctionInvocation[T], v2 : BigInt_2_FunctionInvocation): Boolean_2_IfExpr = appendIndex[T](v0.v, v1.v, v2.v)
  
  @production(3)
  def fd$99[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_Set_0_Equals[TP$0] = v0.v.content
  
  @production(2)
  def fd$100[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_Set_0_SetUnion[TP$0] = v0.v.content
  
  @production(2)
  def fd$101[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_Set_1_SetUnion[TP$0] = v0.v.content
  
  @production(1)
  def fd$102[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_Set_1_ElementOfSet[TP$0] = v0.v.content
  
  @production(1)
  def fd$103[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_Set_1_Equals[TP$0] = v0.v.content
  
  @production(3)
  def fd$104[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_0_Equals[TP$0] = v0.v.apply(v1.v)
  
  @production(2)
  def fd$105[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_1_IfExpr[TP$0] = v0.v.apply(v1.v)
  
  @production(1)
  def fd$106[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_1_IfExpr[TP$0] = v0.v.head
  
  @production(2)
  def fd$107[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_2_IfExpr[TP$0] = v0.v.apply(v1.v)
  
  @production(1)
  def fd$108[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0], v1 : BigInt_1_FunctionInvocation): TP$0_1_Equals[TP$0] = v0.v.apply(v1.v)
  
  @production(1)
  def fd$109(v0 : BigInt_List_0_FunctionInvocation, v1 : BigInt_1_FunctionInvocation): BigInt_List_TOPLEVEL = insSort(v0.v, v1.v)
  
  @production(1)
  def fd$110(v0 : BigInt_List_0_FunctionInvocation): BigInt_List_0_FunctionInvocation = sorted(v0.v)
  
  @production(1)
  def fd$111(v0 : BigInt_List_0_FunctionInvocation, v1 : BigInt_1_FunctionInvocation): BigInt_List_1_CaseClass = insSort(v0.v, v1.v)
  
  @production(1)
  def fd$112[T](v0 : TP$0_List_0_FunctionInvocation[T], v1 : TP$0_1_FunctionInvocation[T]): BigInt_Option_TOPLEVEL = v0.v.find(v1.v)
  
  @production(1)
  def fd$113[TP$0](v0 : TP$0_List_0_FunctionInvocation[TP$0]): TP$0_Option_0_FunctionInvocation[TP$0] = v0.v.lastOption
  
  @production(1)
  def pTP$0Start$0[TP$0](v0 : TP$0_TOPLEVEL[TP$0]): TP$0 = v0.v
  
  @production(1)
  def pTP$0Start$1[TP$0](v0 : TP$0_TOPLEVEL[TP$0]): TP$0 = v0.v
  
  @production(1)
  def pBigIntStart$0(v0 : BigInt_TOPLEVEL): BigInt = v0.v
  
  @production(1)
  def pBooleanStart$0(v0 : Boolean_TOPLEVEL): Boolean = v0.v
  
  @production(1)
  def pTP$0_ListStart$0[TP$0](v0 : TP$0_List_TOPLEVEL[TP$0]): List[TP$0] = v0.v
  
  @production(1)
  def pBigInt_ListStart$0(v0 : BigInt_List_TOPLEVEL): List[BigInt] = v0.v
  
  @production(1)
  def pTP$0_SetStart$0[TP$0](v0 : TP$0_Set_TOPLEVEL[TP$0]): Set[TP$0] = v0.v
  
  @production(1)
  def pTP$0_OptionStart$0[TP$0](v0 : TP$0_Option_TOPLEVEL[TP$0]): Option[TP$0] = v0.v
  
  @production(1)
  def pBigInt_OptionStart$0(v0 : BigInt_Option_TOPLEVEL): Option[BigInt] = v0.v
}

