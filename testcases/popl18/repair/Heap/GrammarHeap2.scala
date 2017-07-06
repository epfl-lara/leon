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

object grammar {
  @label
  implicit class BigInt_List_TOPLEVEL(val v : List[BigInt])
  
  @label
  implicit class BigInt_List_0_FunctionInvocation(val v : List[BigInt])
  
  @label
  implicit class BigInt_List_1_CaseClass(val v : List[BigInt])
  
  @label
  implicit class BigInt_0_Modulo(val v : BigInt)
  
  @label
  implicit class BigInt_0_FunctionInvocation(val v : BigInt)
  
  @label
  implicit class BigInt_1_Plus(val v : BigInt)
  
  @label
  implicit class BigInt_0_FiniteSet(val v : BigInt)
  
  @label
  implicit class BigInt_0_Division(val v : BigInt)
  
  @label
  implicit class BigInt_1_Minus(val v : BigInt)
  
  @label
  implicit class BigInt_0_Lambda(val v : BigInt)
  
  @label
  implicit class BigInt_0_Minus(val v : BigInt)
  
  @label
  implicit class BigInt_0_Plus(val v : BigInt)
  
  @label
  implicit class BigInt_TOPLEVEL(val v : BigInt)
  
  @label
  implicit class BigInt_1_Division(val v : BigInt)
  
  @label
  implicit class BigInt_1_FunctionInvocation(val v : BigInt)
  
  @label
  implicit class BigInt_0_Remainder(val v : BigInt)
  
  @label
  implicit class BigInt_0_UMinus(val v : BigInt)
  
  @label
  implicit class BigInt_1_Remainder(val v : BigInt)
  
  @label
  implicit class BigInt_0_CaseClass(val v : BigInt)
  
  @label
  implicit class Heap$0_0_FunctionInvocation(val v : Heap)
  
  @label
  implicit class Heap$0_0_Tuple(val v : Heap)
  
  @label
  implicit class Heap$0_2_FunctionInvocation(val v : Heap)
  
  @label
  implicit class Heap$0_1_CaseClass(val v : Heap)
  
  @label
  implicit class Heap$0_2_CaseClass(val v : Heap)
  
  @label
  implicit class Heap$0_1_Tuple(val v : Heap)
  
  @label
  implicit class Heap$0_TOPLEVEL(val v : Heap)
  
  @label
  implicit class Heap$0_1_FunctionInvocation(val v : Heap)
  
  @label
  implicit class TP$0_0_Tuple[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_1_Application[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_0_Lambda[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_1_Tuple[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_TOPLEVEL[TP$0](val v : TP$0)
  
  @label
  implicit class TP$0_2_Application[TP$0](val v : TP$0)
  
  @label
  implicit class BigInt_Set_TOPLEVEL(val v : Set[BigInt])
  
  @label
  implicit class BigInt_Set_0_SetUnion(val v : Set[BigInt])
  
  @label
  implicit class BigInt_Set_1_SetUnion(val v : Set[BigInt])
  
  @label
  implicit class BigInt_Option_TOPLEVEL(val v : Option[BigInt])
  
  @production(176)
  def pBigIntVariable$1(): BigInt_TOPLEVEL = variable[BigInt]
  
  @production(86)
  def pBigIntInfiniteIntegerLiteral$12(): BigInt_TOPLEVEL = BigInt(0)
  
  @production(7)
  def pBigIntInfiniteIntegerLiteral$13(): BigInt_TOPLEVEL = BigInt(1)
  
  @production(5)
  def pBigIntInfiniteIntegerLiteral$14(): BigInt_TOPLEVEL = BigInt(-1)
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$15(): BigInt_TOPLEVEL = BigInt(10)
  
  @production(2)
  def pBigIntInfiniteIntegerLiteral$16(): BigInt_TOPLEVEL = BigInt(2)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$17(): BigInt_TOPLEVEL = BigInt(5)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$18(): BigInt_TOPLEVEL = BigInt(6)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$19(): BigInt_TOPLEVEL = BigInt(9)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$20(): BigInt_TOPLEVEL = BigInt(7)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$21(): BigInt_TOPLEVEL = BigInt(3)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$22(): BigInt_TOPLEVEL = BigInt(8)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$23(): BigInt_TOPLEVEL = BigInt(4)
  
  @production(36)
  def pBigIntMinus$1(v0 : BigInt_0_Minus, v1 : BigInt_1_Minus): BigInt_TOPLEVEL = v0.v - v1.v
  
  @production(33)
  def pBigIntPlus$1(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_TOPLEVEL = v0.v + v1.v
  
  @production(11)
  def pBigIntUMinus$1(v0 : BigInt_0_UMinus): BigInt_TOPLEVEL = -v0.v
  
  @production(2)
  def pBigIntDivision$1(v0 : BigInt_0_Division, v1 : BigInt_1_Division): BigInt_TOPLEVEL = v0.v / v1.v
  
  @production(1)
  def pBigIntRemainder$1(v0 : BigInt_0_Remainder, v1 : BigInt_1_Remainder): BigInt_TOPLEVEL = v0.v % v1.v
  
  @production(29)
  def pBigIntVariable$2(): BigInt_0_Minus = variable[BigInt]
  
  @production(2)
  def pBigIntMinus$2(v0 : BigInt_0_Minus, v1 : BigInt_1_Minus): BigInt_0_Minus = v0.v - v1.v
  
  @production(24)
  def pBigIntInfiniteIntegerLiteral$24(): BigInt_1_Minus = BigInt(1)
  
  @production(6)
  def pBigIntVariable$3(): BigInt_1_Minus = variable[BigInt]
  
  @production(19)
  def pBigIntInfiniteIntegerLiteral$25(): BigInt_1_Plus = BigInt(1)
  
  @production(2)
  def pBigIntVariable$4(): BigInt_1_Plus = variable[BigInt]
  
  @production(3)
  def pBigIntInfiniteIntegerLiteral$26(): BigInt_0_Plus = BigInt(1)
  
  @production(3)
  def pBigIntVariable$5(): BigInt_0_Plus = variable[BigInt]
  
  @production(1)
  def pBigIntPlus$2(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_0_Plus = v0.v + v1.v
  
  @production(9)
  def pBigIntVariable$6(): BigInt_0_UMinus = variable[BigInt]
  
  @production(8)
  def pBigIntVariable$7(): BigInt_0_CaseClass = variable[BigInt]
  
  @production(3)
  def pBigIntVariable$8(): BigInt_0_FunctionInvocation = variable[BigInt]
  
  @production(1)
  def pBigIntPlus$3(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_0_FunctionInvocation = v0.v + v1.v
  
  @production(3)
  def pBigIntVariable$9(): BigInt_1_FunctionInvocation = variable[BigInt]
  
  @production(2)
  def pBigIntVariable$10(): BigInt_0_FiniteSet = variable[BigInt]
  
  @production(2)
  def pBigIntPlus$4(v0 : BigInt_0_Plus, v1 : BigInt_1_Plus): BigInt_0_Lambda = v0.v + v1.v
  
  @production(2)
  def pBigIntVariable$11(): BigInt_0_Modulo = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$27(): BigInt_1_Division = BigInt(2)
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$28(): BigInt_1_Division = BigInt(10)
  
  @production(1)
  def pBigIntVariable$12(): BigInt_0_Division = variable[BigInt]
  
  @production(1)
  def pBigIntVariable$13(): BigInt_0_Remainder = variable[BigInt]
  
  @production(1)
  def pBigIntInfiniteIntegerLiteral$29(): BigInt_1_Remainder = BigInt(10)
  
  @production(272)
  def pTP$0Variable$1[TP$0](): TP$0_TOPLEVEL[TP$0] = variable[TP$0]
  
  @production(46)
  def pTP$0Variable$2[TP$0](): TP$0_1_Application[TP$0] = variable[TP$0]
  
  @production(18)
  def pTP$0Variable$3[TP$0](): TP$0_1_Tuple[TP$0] = variable[TP$0]
  
  @production(16)
  def pTP$0Variable$4[TP$0](): TP$0_0_Tuple[TP$0] = variable[TP$0]
  
  @production(10)
  def pTP$0Variable$5[TP$0](): TP$0_2_Application[TP$0] = variable[TP$0]
  
  @production(1)
  def pTP$0Variable$6[TP$0](): TP$0_0_Lambda[TP$0] = variable[TP$0]
  
  @production(33)
  def pHeap$0Variable$1(): Heap$0_TOPLEVEL = variable[Heap]
  
  @production(2)
  def pHeap$0Node0$0(v0 : BigInt_0_CaseClass, v1 : Heap$0_1_CaseClass, v2 : Heap$0_2_CaseClass): Heap$0_TOPLEVEL = Node(v0.v, v1.v, v2.v)
  
  @production(23)
  def pHeap$0Variable$2(): Heap$0_0_FunctionInvocation = variable[Heap]
  
  @production(1)
  def pHeap$0Node0$1(v0 : BigInt_0_CaseClass, v1 : Heap$0_1_CaseClass, v2 : Heap$0_2_CaseClass): Heap$0_0_FunctionInvocation = Node(v0.v, v1.v, v2.v)
  
  @production(6)
  def pHeap$0Variable$3(): Heap$0_1_FunctionInvocation = variable[Heap]
  
  @production(2)
  def pHeap$0Variable$4(): Heap$0_1_CaseClass = variable[Heap]
  
  @production(1)
  def pHeap$0Leaf0$0(): Heap$0_1_CaseClass = Leaf()
  
  @production(2)
  def pHeap$0Variable$5(): Heap$0_2_CaseClass = variable[Heap]
  
  @production(1)
  def pHeap$0Leaf0$1(): Heap$0_2_CaseClass = Leaf()
  
  @production(1)
  def pHeap$0Variable$6(): Heap$0_0_Tuple = variable[Heap]
  
  @production(1)
  def pHeap$0Variable$7(): Heap$0_1_Tuple = variable[Heap]
  
  @production(7)
  def pBigInt_ListVariable$1(): BigInt_List_TOPLEVEL = variable[List[BigInt]]
  
  @production(4)
  def pBigInt_ListCons0$0(v0 : BigInt_0_CaseClass, v1 : BigInt_List_1_CaseClass): BigInt_List_TOPLEVEL = Cons[BigInt](v0.v, v1.v)
  
  @production(2)
  def pBigInt_ListNil0$0(): BigInt_List_TOPLEVEL = Nil[BigInt]()
  
  @production(3)
  def pBigInt_ListVariable$2(): BigInt_List_0_FunctionInvocation = variable[List[BigInt]]
  
  @production(1)
  def pBigInt_ListNil0$1(): BigInt_List_1_CaseClass = Nil[BigInt]()
  
  @production(1)
  def pBigInt_ListVariable$3(): BigInt_List_1_CaseClass = variable[List[BigInt]]
  
  @production(3)
  def pBigInt_SetSetUnion$1(v0 : BigInt_Set_0_SetUnion, v1 : BigInt_Set_1_SetUnion): BigInt_Set_TOPLEVEL = v0.v ++ v1.v
  
  @production(1)
  def pBigInt_SetFiniteSet$2(): BigInt_Set_TOPLEVEL = Set[BigInt]()
  
  @production(1)
  def pBigInt_SetSetUnion$2(v0 : BigInt_Set_0_SetUnion, v1 : BigInt_Set_1_SetUnion): BigInt_Set_0_SetUnion = v0.v ++ v1.v
  
  @production(2)
  def pBigInt_SetFiniteSet$3(v0 : BigInt_0_FiniteSet): BigInt_Set_1_SetUnion = Set[BigInt](v0.v)
  
  @production(1)
  def pBigInt_OptionSome0$0(v0 : BigInt_0_CaseClass): BigInt_Option_TOPLEVEL = Some[BigInt](v0.v)
  
  @production(1)
  def pBigInt_OptionNone0$0(): BigInt_Option_TOPLEVEL = None[BigInt]()
  
  @production(4)
  def fd$3(v0 : Heap$0_0_FunctionInvocation): BigInt_TOPLEVEL = v0.v.rank
  
  @production(2)
  def fd$4(v0 : Heap$0_0_FunctionInvocation): BigInt_TOPLEVEL = heapSize(v0.v)
  
  @production(3)
  def fd$5(v0 : Heap$0_0_FunctionInvocation): BigInt_0_Plus = heapSize(v0.v)
  
  @production(2)
  def fd$6(v0 : Heap$0_0_FunctionInvocation): BigInt_1_Plus = heapSize(v0.v)
  
  @production(1)
  def fd$7(v0 : BigInt_0_FunctionInvocation, v1 : BigInt_1_FunctionInvocation): BigInt_1_Plus = max(v0.v, v1.v)
  
  @production(1)
  def fd$8(v0 : Heap$0_0_FunctionInvocation): BigInt_0_FunctionInvocation = v0.v.rank
  
  @production(1)
  def fd$9(v0 : Heap$0_0_FunctionInvocation): BigInt_1_FunctionInvocation = v0.v.rank
  
  @production(3)
  def fd$10(v0 : Heap$0_0_FunctionInvocation): BigInt_Set_0_SetUnion = v0.v.content
  
  @production(2)
  def fd$11(v0 : Heap$0_0_FunctionInvocation): BigInt_Set_TOPLEVEL = v0.v.content
  
  @production(2)
  def fd$12(v0 : Heap$0_0_FunctionInvocation): BigInt_Set_1_SetUnion = v0.v.content
  
  @production(1)
  def pTP$0Start$0[TP$0](v0 : TP$0_TOPLEVEL[TP$0]): TP$0 = v0.v
  
  @production(1)
  def pBigIntStart$0(v0 : BigInt_TOPLEVEL): BigInt = v0.v
  
  @production(1)
  def pBigInt_ListStart$0(v0 : BigInt_List_TOPLEVEL): List[BigInt] = v0.v
  
  @production(1)
  def pBigInt_SetStart$0(v0 : BigInt_Set_TOPLEVEL): Set[BigInt] = v0.v
  
  @production(1)
  def pBigInt_OptionStart$0(v0 : BigInt_Option_TOPLEVEL): Option[BigInt] = v0.v
  
  @production(1)
  def pHeap$0Start$0(v0 : Heap$0_TOPLEVEL): Heap = v0.v
}

