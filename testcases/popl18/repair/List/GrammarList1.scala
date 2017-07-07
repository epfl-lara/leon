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
  @production(192)
  @tag("top")
  def pTP$0_ListVariable[TP$0](): List[TP$0] = variable[List[TP$0]]
  
  @production(24)
  @tag("top")
  def pTP$0_ListCons[TP$0](h : TP$0, t : List[TP$0]): List[TP$0] = Cons[TP$0](h, t)
  
  @production(21)
  @tag("top")
  def pTP$0_ListNil[TP$0](): List[TP$0] = Nil[TP$0]()
  
  @production(6)
  @tag("ite")
  def pTP$0_ListIfExpr[TP$0](v0 : Boolean, v1 : List[TP$0], v2 : List[TP$0]): List[TP$0] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(77)
  @tag("top")
  def pBigIntVariable(): BigInt = variable[BigInt]
  
  @production(26)
  @tag("0")
  def pBigIntInfiniteIntegerLiteral$0(): BigInt = BigInt(0)
  
  @production(15)
  @tag("1")
  def pBigIntInfiniteIntegerLiteral$1(): BigInt = BigInt(1)
  
  @production(2)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$2(): BigInt = BigInt(2)
  
  @production(13)
  @tag("minus")
  def pBigIntMinus(v0 : BigInt, v1 : BigInt): BigInt = v0 - v1
  
  @production(10)
  @tag("plus")
  def pBigIntPlus(v0 : BigInt, v1 : BigInt): BigInt = v0 + v1
  
  @production(1)
  @tag("div")
  def pBigIntDivision(v0 : BigInt, v1 : BigInt): BigInt = v0 / v1
  
  @production(1)
  @tag("ite")
  def pBigIntIfExpr(v0 : Boolean, v1 : BigInt, v2 : BigInt): BigInt = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(1)
  @tag("top")
  def pBigIntRemainder(v0 : BigInt, v1 : BigInt): BigInt = v0 % v1
  
  @production(7)
  @tag("equals")
  def pBooleanEquals[TP$0](v0 : List[TP$0], v1 : List[TP$0]): Boolean = v0 == v1
  
  @production(13)
  @tag("equals")
  def pBooleanEquals(v0 : BigInt, v1 : BigInt): Boolean = v0 == v1
  
  @production(3)
  @tag("equals")
  def pBooleanEquals[TP$0](v0 : Set[TP$0], v1 : Set[TP$0]): Boolean = v0 == v1
  
  @production(8)
  @tag("equals")
  def pBooleanEquals[TP$0](v0 : TP$0, v1 : TP$0): Boolean = v0 == v1
  
  @production(1)
  @tag("equals")
  def pBooleanEquals(v0 : Boolean, v1 : Boolean): Boolean = v0 == v1
  
  @production(14)
  @tag("booleanC")
  def pBooleanBooleanLiteral$0(): Boolean = true
  
  @production(3)
  @tag("booleanC")
  def pBooleanBooleanLiteral$1(): Boolean = false
  
  @production(16)
  @tag("top")
  def pBooleanLessThan(v0 : BigInt, v1 : BigInt): Boolean = v0 < v1
  
  @production(11)
  @tag("and")
  def pBooleanAnd(v0 : Boolean, v1 : Boolean): Boolean = v0 && v1
  
  @production(9)
  @tag("top")
  def pBooleanVariable(): Boolean = variable[Boolean]
  
  @production(8)
  @tag("top")
  def pBooleanLessEquals(v0 : BigInt, v1 : BigInt): Boolean = v0 <= v1
  
  @production(4)
  @tag("not")
  def pBooleanNot(v0 : Boolean): Boolean = !v0
  
  @production(2)
  @tag("ite")
  def pBooleanIfExpr(v0 : Boolean, v1 : Boolean, v2 : Boolean): Boolean = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(1)
  @tag("top")
  def pBooleanElementOfSet[TP$0](v0 : TP$0, v1 : Set[TP$0]): Boolean = v1.contains(v0)
  
  @production(1)
  @tag("or")
  def pBooleanOr(v0 : Boolean, v1 : Boolean): Boolean = v0 || v1
  
  @production(72)
  @tag("top")
  def pTP$0Variable[TP$0](): TP$0 = variable[TP$0]
  
  @production(3)
  @tag("ite")
  def pTP$0IfExpr[TP$0](v0 : Boolean, v1 : TP$0, v2 : TP$0): TP$0 = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(7)
  @tag("top")
  def pBigInt_ListVariable(): List[BigInt] = variable[List[BigInt]]
  
  @production(3)
  @tag("top")
  def pBigInt_ListCons(h : BigInt, t : List[BigInt]): List[BigInt] = Cons[BigInt](h, t)
  
  @production(2)
  @tag("top")
  def pBigInt_ListNil(): List[BigInt] = Nil[BigInt]()
  
  @production(1)
  @tag("ite")
  def pBigInt_ListIfExpr(v0 : Boolean, v1 : List[BigInt], v2 : List[BigInt]): List[BigInt] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(1)
  @tag("top")
  def pTP$0_SetFiniteSet[TP$0](): Set[TP$0] = Set[TP$0]()
  
  @production(2)
  @tag("top")
  def pTP$0_SetFiniteSet[TP$0](v0 : TP$0): Set[TP$0] = Set[TP$0](v0)
  
  @production(3)
  @tag("top")
  def pTP$0_SetSetUnion[TP$0](v0 : Set[TP$0], v1 : Set[TP$0]): Set[TP$0] = v0 ++ v1
  
  @production(2)
  @tag("top")
  def pBigInt_OptionSome(v : BigInt): Option[BigInt] = Some[BigInt](v)
  
  @production(2)
  @tag("top")
  def pBigInt_OptionNone(): Option[BigInt] = None[BigInt]()
  
  @production(2)
  @tag("top")
  def pTP$0_OptionSome[TP$0](v : TP$0): Option[TP$0] = Some[TP$0](v)
  
  @production(2)
  @tag("top")
  def pTP$0_OptionNone[TP$0](): Option[TP$0] = None[TP$0]()
  
  @tag("top")
  @production(13)
  def fd$0[TP$0](v0 : List[TP$0], v1 : List[TP$0]): List[TP$0] = v0 ++ v1
  
  @tag("top")
  @production(8)
  def fd$1[TP$0](v0 : List[TP$0], v1 : TP$0): List[TP$0] = v0.:+(v1)
  
  @tag("top")
  @production(7)
  def fd$2[TP$0](v0 : List[TP$0]): List[TP$0] = v0.reverse
  
  @tag("top")
  @production(5)
  def fd$3[TP$0](v0 : List[TP$0], v1 : BigInt): List[TP$0] = v0.drop(v1)
  
  @tag("top")
  @production(4)
  def fd$4[TP$0](v0 : List[TP$0], v1 : BigInt): List[TP$0] = v0.take(v1)
  
  @tag("top")
  @production(3)
  def fd$5[TP$0](v0 : List[TP$0], v1 : TP$0): List[TP$0] = v0 - v1
  
  @tag("top")
  @production(2)
  def fd$6[TP$0](v0 : List[TP$0], v1 : List[TP$0]): List[TP$0] = v0 -- v1
  
  @tag("top")
  @production(2)
  def fd$7[TP$0](v0 : List[TP$0], v1 : List[TP$0]): List[TP$0] = v0.&(v1)
  
  @tag("top")
  @production(2)
  def fd$8[TP$0](v0 : List[TP$0], v1 : BigInt, v2 : TP$0): List[TP$0] = v0.pad(v1, v2)
  
  @tag("top")
  @production(2)
  def fd$9[TP$0](v0 : List[TP$0], v1 : BigInt, v2 : List[TP$0]): List[TP$0] = v0.insertAt(v1, v2)
  
  @tag("top")
  @production(2)
  def fd$10[TP$0](v0 : List[TP$0], v1 : BigInt, v2 : List[TP$0]): List[TP$0] = v0.replaceAt(v1, v2)
  
  @tag("top")
  @production(1)
  def fd$11[TP$0](v0 : List[TP$0]): List[TP$0] = v0.tail
  
  @tag("top")
  @production(1)
  def fd$12[TP$0](v0 : List[TP$0], v1 : TP$0, v2 : TP$0): List[TP$0] = v0.replace(v1, v2)
  
  @tag("top")
  @production(1)
  def fd$13[TP$0](v0 : List[TP$0]): List[TP$0] = v0.init
  
  @tag("top")
  @production(1)
  def fd$14[TP$0](v0 : List[TP$0]): List[TP$0] = v0.unique
  
  @tag("top")
  @production(1)
  def fd$15[TP$0](v0 : List[TP$0], v1 : BigInt): List[TP$0] = v0.rotate(v1)
  
  @tag("top")
  @production(29)
  def fd$16[T](v0 : List[T]): BigInt = v0.size
  
  @tag("top")
  @production(2)
  def fd$17[T](v0 : List[T], v1 : T): BigInt = v0.count(v1)
  
  @tag("top")
  @production(4)
  def fd$18[T](v0 : List[T], v1 : T): Boolean = v0.contains(v1)
  
  @tag("top")
  @production(2)
  def fd$19[T](v0 : List[T], v1 : T, v2 : BigInt): Boolean = snocIndex[T](v0, v1, v2)
  
  @tag("top")
  @production(2)
  def fd$20[T](v0 : List[T], v1 : T): Boolean = snocReverse[T](v0, v1)
  
  @tag("top")
  @production(1)
  def fd$21(v0 : List[BigInt]): Boolean = isSorted(v0)
  
  @tag("top")
  @production(1)
  def fd$22[T](v0 : List[T], v1 : BigInt): Boolean = reverseIndex[T](v0, v1)
  
  @tag("top")
  @production(1)
  def fd$23[T](v0 : List[T], v1 : List[T], v2 : BigInt): Boolean = appendIndex[T](v0, v1, v2)
  
  @tag("top")
  @production(1)
  def fd$24[T](v0 : List[T], v1 : List[T], v2 : List[T]): Boolean = appendAssoc[T](v0, v1, v2)
  
  @tag("top")
  @production(1)
  def fd$25[T](v0 : List[T], v1 : T): Boolean = snocIsAppend[T](v0, v1)
  
  @tag("top")
  @production(1)
  def fd$26[T](v0 : List[T], v1 : List[T], v2 : T): Boolean = snocAfterAppend[T](v0, v1, v2)
  
  @tag("top")
  @production(1)
  def fd$27[T](v0 : List[T]): Boolean = reverseReverse[T](v0)
  
  @tag("top")
  @production(9)
  def fd$28[TP$0](v0 : List[TP$0]): Set[TP$0] = v0.content
  
  @tag("top")
  @production(8)
  def fd$29[TP$0](v0 : List[TP$0], v1 : BigInt): TP$0 = v0.apply(v1)
  
  @tag("top")
  @production(1)
  def fd$30[TP$0](v0 : List[TP$0]): TP$0 = v0.head
  
  @tag("top")
  @production(2)
  def fd$31(v0 : List[BigInt], v1 : BigInt): List[BigInt] = insSort(v0, v1)
  
  @tag("top")
  @production(1)
  def fd$32(v0 : List[BigInt]): List[BigInt] = sorted(v0)
  
  @tag("top")
  @production(1)
  def fd$33[T](v0 : List[T], v1 : T): Option[BigInt] = v0.find(v1)
  
  @tag("top")
  @production(1)
  def fd$34[TP$0](v0 : List[TP$0]): Option[TP$0] = v0.lastOption
}

