package leon
package grammar
import leon.collection._
import leon.lang._
import leon.lang.synthesis._
import leon.math._
import annotation.grammar._

object Grammar {
  @production(1784)
  @tag("and")
  def pBooleanAnd$0(v0$0 : Boolean, v1$7 : Boolean): Boolean = v0$0 && v1$7
  
  @production(1108)
  @tag("top")
  def pBooleanVariable$0(): Boolean = variable[Boolean]
  
  @production(7)
  @tag("top")
  def pBooleanLessEquals$0(v0$1 : Real, v1$8 : Real): Boolean = v0$1 <= v1$8
  
  @production(349)
  @tag("top")
  def pBooleanLessEquals$1(v0$2 : BigInt, v1$9 : BigInt): Boolean = v0$2 <= v1$9
  
  @production(597)
  @tag("top")
  def pBooleanLessEquals$2(v0$3 : Int, v1$10 : Int): Boolean = v0$3 <= v1$10
  
  @production(9)
  @tag("equals")
  def pBooleanEquals$0(v0$4 : Real, v1$11 : Real): Boolean = v0$4 == v1$11
  
  @production(3)
  @tag("equals")
  def pBooleanEquals$1(v0$5 : Option[Boolean], v1$12 : Option[Boolean]): Boolean = v0$5 == v1$12
  
  @production(22)
  @tag("equals")
  def pBooleanEquals$2[TP$0](v0$6 : TP$0, v1$13 : TP$0): Boolean = v0$6 == v1$13
  
  @production(18)
  @tag("equals")
  def pBooleanEquals$3(v0$7 : List[BigInt], v1$14 : List[BigInt]): Boolean = v0$7 == v1$14
  
  @production(4)
  @tag("equals")
  def pBooleanEquals$4(v0$8 : Char, v1$15 : Char): Boolean = v0$8 == v1$15
  
  @production(350)
  @tag("equals")
  def pBooleanEquals$5(v0$9 : BigInt, v1$16 : BigInt): Boolean = v0$9 == v1$16
  
  @production(75)
  @tag("equals")
  def pBooleanEquals$6(v0$10 : Set[Int], v1$17 : Set[Int]): Boolean = v0$10 == v1$17
  
  @production(2)
  @tag("equals")
  def pBooleanEquals$7(v0$11 : Option[BigInt], v1$18 : Option[BigInt]): Boolean = v0$11 == v1$18
  
  @production(42)
  @tag("equals")
  def pBooleanEquals$8[TP$0](v0$12 : List[TP$0], v1$19 : List[TP$0]): Boolean = v0$12 == v1$19
  
  @production(230)
  @tag("equals")
  def pBooleanEquals$9(v0$13 : Int, v1$20 : Int): Boolean = v0$13 == v1$20
  
  @production(24)
  @tag("equals")
  def pBooleanEquals$10(v0$14 : Set[BigInt], v1$21 : Set[BigInt]): Boolean = v0$14 == v1$21
  
  @production(24)
  @tag("equals")
  def pBooleanEquals$11[TP$0](v0$15 : Set[TP$0], v1$22 : Set[TP$0]): Boolean = v0$15 == v1$22
  
  @production(2)
  @tag("equals")
  def pBooleanEquals$12(v0$16 : List[Char], v1$23 : List[Char]): Boolean = v0$16 == v1$23
  
  @production(1)
  @tag("equals")
  def pBooleanEquals$13(v0$17 : Unit, v1$24 : Unit): Boolean = v0$17 == v1$24
  
  @production(82)
  @tag("equals")
  def pBooleanEquals$14(v0$18 : Boolean, v1$25 : Boolean): Boolean = v0$18 == v1$25
  
  @production(476)
  @tag("booleanC")
  def pBooleanBooleanLiteral$0(): Boolean = true
  
  @production(221)
  @tag("booleanC")
  def pBooleanBooleanLiteral$1(): Boolean = false
  
  @production(9)
  @tag("top")
  def pBooleanLessThan$0(v0$19 : Real, v1$26 : Real): Boolean = v0$19 < v1$26
  
  @production(242)
  @tag("top")
  def pBooleanLessThan$1(v0$20 : BigInt, v1$27 : BigInt): Boolean = v0$20 < v1$27
  
  @production(436)
  @tag("top")
  def pBooleanLessThan$2(v0$21 : Int, v1$28 : Int): Boolean = v0$21 < v1$28
  
  @production(486)
  @tag("not")
  def pBooleanNot$0(v0$22 : Boolean): Boolean = !v0$22
  
  @production(154)
  @tag("ite")
  def pBooleanIfExpr$0(v0$23 : Boolean, v1$29 : Boolean, v2$9 : Boolean): Boolean = if (v0$23) {
    v1$29
  } else {
    v2$9
  }
  
  @production(139)
  @tag("or")
  def pBooleanOr$0(v0$24 : Boolean, v1$30 : Boolean): Boolean = v0$24 || v1$30
  
  @production(23)
  @tag("top")
  def pBooleanElementOfSet$0(v0$25 : BigInt, v1$31 : Set[BigInt]): Boolean = v1$31.contains(v0$25)
  
  @production(16)
  @tag("top")
  def pBooleanElementOfSet$1[TP$0](v0$26 : TP$0, v1$32 : Set[TP$0]): Boolean = v1$32.contains(v0$26)
  
  @production(25)
  @tag("top")
  def pBooleanElementOfSet$2(v0$27 : Int, v1$33 : Set[Int]): Boolean = v1$33.contains(v0$27)
  
  @production(50)
  @tag("top")
  def pBooleanImplies$0(v0$28 : Boolean, v1$34 : Boolean): Boolean = v0$28 ==> v1$34
  
  @production(9)
  @tag("top")
  def pBooleanSubsetOf$0[TP$0](v0$29 : Set[TP$0], v1$35 : Set[TP$0]): Boolean = v0$29.subsetOf(v1$35)
  
  @production(3)
  @tag("top")
  def pBooleanSubsetOf$1(v0$30 : Set[Int], v1$36 : Set[Int]): Boolean = v0$30.subsetOf(v1$36)
  
  @production(3487)
  @tag("top")
  def pIntVariable$0(): Int = variable[Int]
  
  @production(667)
  @tag("0")
  def pIntIntLiteral$0(): Int = 0
  
  @production(390)
  @tag("1")
  def pIntIntLiteral$1(): Int = 1
  
  @production(87)
  @tag("const")
  def pIntIntLiteral$2(): Int = 2
  
  @production(46)
  @tag("const")
  def pIntIntLiteral$3(): Int = -1

  @production(43)
  @tag("const")
  def pIntIntLiteral$4(): Int = 5
  
  @production(25)
  @tag("const")
  def pIntIntLiteral$5(): Int = 3
/* FIXME: Manually removed  
  @production(12)
  @tag("const")
  def pIntIntLiteral$6(): Int = 32
  
  @production(8)
  @tag("const")
  def pIntIntLiteral$7(): Int = 10
  
  @production(8)
  @tag("const")
  def pIntIntLiteral$8(): Int = 4
  
  @production(4)
  @tag("const")
  def pIntIntLiteral$9(): Int = 33
  
  @production(4)
  @tag("const")
  def pIntIntLiteral$10(): Int = -2
  
  @production(3)
  @tag("const")
  def pIntIntLiteral$11(): Int = 31
  
  @production(2)
  @tag("const")
  def pIntIntLiteral$12(): Int = 1073741824
  
  @production(2)
  @tag("const")
  def pIntIntLiteral$13(): Int = 6
  
  @production(2)
  @tag("const")
  def pIntIntLiteral$14(): Int = 7
  
  @production(1)
  @tag("const")
  def pIntIntLiteral$15(): Int = 42
  
  @production(1)
  @tag("const")
  def pIntIntLiteral$16(): Int = 349
  
  @production(1)
  @tag("const")
  def pIntIntLiteral$17(): Int = -1000
  
  @production(1)
  @tag("const")
  def pIntIntLiteral$18(): Int = 147483648
  
  @production(1)
  @tag("const")
  def pIntIntLiteral$19(): Int = -10
  
  @production(1)
  @tag("const")
  def pIntIntLiteral$20(): Int = 100000000
  
  @production(1)
  @tag("const")
  def pIntIntLiteral$21(): Int = -33
  
  @production(1)
  @tag("const")
  def pIntIntLiteral$22(): Int = 358
  
  @production(1)
  @tag("const")
  def pIntIntLiteral$23(): Int = 122
  */
  @production(299)
  @tag("plus")
  def pIntBVPlus$0(v0$31 : Int, v1$37 : Int): Int = v0$31 + v1$37
  
  @production(104)
  @tag("minus")
  def pIntBVMinus$0(v0$32 : Int, v1$38 : Int): Int = v0$32 - v1$38
  
  @production(31)
  @tag("ite")
  def pIntIfExpr$0(v0$33 : Boolean, v1$39 : Int, v2$10 : Int): Int = if (v0$33) {
    v1$39
  } else {
    v2$10
  }
  
  @production(20)
  @tag("times")
  def pIntBVTimes$0(v0$34 : Int, v1$40 : Int): Int = v0$34 * v1$40
  
  @production(11)
  @tag("top")
  def pIntBVDivision$0(v0$35 : Int, v1$41 : Int): Int = v0$35 / v1$41
  
  @production(10)
  @tag("top")
  def pIntBVAShiftRight$0(v0$36 : Int, v1$42 : Int): Int = v0$36 >> v1$42
  
  @production(6)
  @tag("top")
  def pIntBVAnd$0(v0$37 : Int, v1$43 : Int): Int = v0$37 & v1$43
  
  @production(5)
  @tag("top")
  def pIntBVXOr$0(v0$38 : Int, v1$44 : Int): Int = v0$38 ^ v1$44
  
  @production(4)
  @tag("top")
  def pIntBVShiftLeft$0(v0$39 : Int, v1$45 : Int): Int = v0$39 << v1$45
  
  @production(3)
  @tag("top")
  def pIntBVLShiftRight$0(v0$40 : Int, v1$46 : Int): Int = v0$40 >>> v1$46
  
  @production(3)
  @tag("top")
  def pIntBVOr$0(v0$41 : Int, v1$47 : Int): Int = v0$41 | v1$47
  
  @production(3)
  @tag("top")
  def pIntBVRemainder$0(v0$42 : Int, v1$48 : Int): Int = v0$42 % v1$48
  
  @production(2)
  @tag("top")
  def pIntBVUMinus$0(v0$43 : Int): Int = -v0$43
  
  @production(2671)
  @tag("top")
  def pBigIntVariable$0(): BigInt = variable[BigInt]
  
  @production(562)
  @tag("0")
  def pBigIntInfiniteIntegerLiteral$0(): BigInt = BigInt(0)
  
  @production(375)
  @tag("1")
  def pBigIntInfiniteIntegerLiteral$1(): BigInt = BigInt(1)
  
  @production(97)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$2(): BigInt = BigInt(2)
  /* FIXME: Manually removed 
  @production(23)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$3(): BigInt = BigInt(10)
  
  @production(14)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$4(): BigInt = BigInt(5)
  
  @production(12)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$5(): BigInt = BigInt(60)
  */
  @production(11)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$6(): BigInt = BigInt(-1)
  /*
  @production(10)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$7(): BigInt = BigInt(4)
  
  @production(7)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$8(): BigInt = BigInt(6)
  
  @production(7)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$9(): BigInt = BigInt(3)
  
  @production(6)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$10(): BigInt = BigInt(7)
  
  @production(5)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$11(): BigInt = BigInt(-2)
  
  @production(4)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$12(): BigInt = BigInt(3600)
  
  @production(4)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$13(): BigInt = BigInt(50)
  
  @production(4)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$14(): BigInt = BigInt(8)
  
  @production(3)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$15(): BigInt = BigInt(32)
  
  @production(2)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$16(): BigInt = BigInt(35)
  
  @production(2)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$17(): BigInt = BigInt(30)
  
  @production(2)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$18(): BigInt = BigInt(100)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$19(): BigInt = BigInt(1001)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$20(): BigInt = BigInt(-3)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$21(): BigInt = BigInt(9)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$22(): BigInt = BigInt(53)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$23(): BigInt = BigInt(13)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$24(): BigInt = BigInt(17)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$25(): BigInt = BigInt(59)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$26(): BigInt = BigInt(-10)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$27(): BigInt = BigInt(31)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$28(): BigInt = BigInt(40)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$29(): BigInt = BigInt(300)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$30(): BigInt = BigInt(15)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$31(): BigInt = BigInt(200)
  */
  @production(281)
  @tag("minus")
  def pBigIntMinus$0(v0$44 : BigInt, v1$49 : BigInt): BigInt = v0$44 - v1$49
  
  @production(214)
  @tag("plus")
  def pBigIntPlus$0(v0$45 : BigInt, v1$50 : BigInt): BigInt = v0$45 + v1$50
  
  @production(143)
  @tag("times")
  def pBigIntTimes$0(v0$46 : BigInt, v1$51 : BigInt): BigInt = v0$46 * v1$51
  
  @production(46)
  @tag("ite")
  def pBigIntIfExpr$0(v0$47 : Boolean, v1$52 : BigInt, v2$11 : BigInt): BigInt = if (v0$47) {
    v1$52
  } else {
    v2$11
  }
  
  @production(34)
  @tag("div")
  def pBigIntDivision$0(v0$48 : BigInt, v1$53 : BigInt): BigInt = v0$48 / v1$53
  
  @production(28)
  @tag("top")
  def pBigIntUMinus$0(v0$49 : BigInt): BigInt = -v0$49
  
  @production(19)
  @tag("top")
  def pBigIntRemainder$0(v0$50 : BigInt, v1$54 : BigInt): BigInt = v0$50 % v1$54
  
  @production(2)
  @tag("mod")
  def pBigIntModulo$0(v0$51 : BigInt, v1$55 : BigInt): BigInt = v0$51 mod v1$55
  
  @production(880)
  @tag("top")
  def pTP$0_ListVariable$0[TP$0](): List[TP$0] = variable[List[TP$0]]
  
  @production(62)
  @tag("top")
  def pTP$0_ListCons[TP$0](h$782 : TP$0, t$1779 : List[TP$0]): List[TP$0] = Cons[TP$0](h$782, t$1779)
  
  @production(80)
  @tag("top")
  def pTP$0_ListNil[TP$0](): List[TP$0] = Nil[TP$0]()
  
  @production(16)
  @tag("ite")
  def pTP$0_ListIfExpr$0[TP$0](v0$52 : Boolean, v1$56 : List[TP$0], v2$12 : List[TP$0]): List[TP$0] = if (v0$52) {
    v1$56
  } else {
    v2$12
  }
  
  @production(618)
  @tag("top")
  def pTP$0Variable$0[TP$0](): TP$0 = variable[TP$0]
  
  @production(4)
  @tag("ite")
  def pTP$0IfExpr$0[TP$0](v0$53 : Boolean, v1$57 : TP$0, v2$13 : TP$0): TP$0 = if (v0$53) {
    v1$57
  } else {
    v2$13
  }
  
  @production(271)
  @tag("top")
  def pBigInt_ListVariable$0(): List[BigInt] = variable[List[BigInt]]
  
  @production(40)
  @tag("top")
  def pBigInt_ListCons(h$783 : BigInt, t$1780 : List[BigInt]): List[BigInt] = Cons[BigInt](h$783, t$1780)
  
  @production(31)
  @tag("top")
  def pBigInt_ListNil(): List[BigInt] = Nil[BigInt]()
  
  @production(5)
  @tag("ite")
  def pBigInt_ListIfExpr$0(v0$54 : Boolean, v1$58 : List[BigInt], v2$14 : List[BigInt]): List[BigInt] = if (v0$54) {
    v1$58
  } else {
    v2$14
  }
  
  @production(215)
  @tag("const")
  def pUnitUnitLiteral$0(): Unit = ()
  
  @production(113)
  @tag("top")
  def pUnitVariable$0(): Unit = variable[Unit]
  
  @production(152)
  @tag("top")
  def pTP$0_SetVariable$0[TP$0](): Set[TP$0] = variable[Set[TP$0]]
  
  @production(35)
  @tag("top")
  def pTP$0_SetSetUnion$0[TP$0](v0$55 : Set[TP$0], v1$59 : Set[TP$0]): Set[TP$0] = v0$55 ++ v1$59
  
  @production(13)
  @tag("top")
  def pTP$0_SetFiniteSet$0[TP$0](v0$56 : TP$0): Set[TP$0] = Set[TP$0](v0$56)
  
  @production(12)
  @tag("top")
  def pTP$0_SetFiniteSet$1[TP$0](): Set[TP$0] = Set[TP$0]()
  
  @production(3)
  @tag("ite")
  def pTP$0_SetIfExpr$0[TP$0](v0$57 : Boolean, v1$60 : Set[TP$0], v2$15 : Set[TP$0]): Set[TP$0] = if (v0$57) {
    v1$60
  } else {
    v2$15
  }
  
  @production(3)
  @tag("top")
  def pTP$0_SetSetDifference$0[TP$0](v0$58 : Set[TP$0], v1$61 : Set[TP$0]): Set[TP$0] = v0$58 -- v1$61
  
  @production(2)
  @tag("top")
  def pTP$0_SetSetIntersection$0[TP$0](v0$59 : Set[TP$0], v1$62 : Set[TP$0]): Set[TP$0] = v0$59 & v1$62
  
  @production(108)
  @tag("top")
  def pInt_SetSetUnion$0(v0$60 : Set[Int], v1$63 : Set[Int]): Set[Int] = v0$60 ++ v1$63
  
  @production(53)
  @tag("top")
  def pInt_SetFiniteSet$0(v0$61 : Int): Set[Int] = Set[Int](v0$61)
  
  @production(3)
  @tag("top")
  def pInt_SetFiniteSet$1(): Set[Int] = Set[Int]()
  
  @production(44)
  @tag("top")
  def pInt_SetVariable$0(): Set[Int] = variable[Set[Int]]
  
  @production(1)
  @tag("top")
  def pInt_SetSetDifference$0(v0$62 : Set[Int], v1$64 : Set[Int]): Set[Int] = v0$62 -- v1$64
  
  @production(2)
  @tag("top")
  def pBigInt_SetFiniteSet$0(v0$63 : BigInt, v1$65 : BigInt, v2$16 : BigInt): Set[BigInt] = Set[BigInt](v0$63, v1$65, v2$16)
  
  @production(2)
  @tag("top")
  def pBigInt_SetFiniteSet$1(v0$64 : BigInt, v1$66 : BigInt): Set[BigInt] = Set[BigInt](v0$64, v1$66)
  
  @production(22)
  @tag("top")
  def pBigInt_SetFiniteSet$2(v0$65 : BigInt): Set[BigInt] = Set[BigInt](v0$65)
  
  @production(3)
  @tag("top")
  def pBigInt_SetFiniteSet$3(): Set[BigInt] = Set[BigInt]()
  
  @production(3)
  @tag("top")
  def pBigInt_SetFiniteSet$4(v0$66 : BigInt, v1$67 : BigInt, v2$17 : BigInt, v3$0 : BigInt): Set[BigInt] = Set[BigInt](v0$66, v1$67, v2$17, v3$0)
  
  @production(3)
  @tag("top")
  def pBigInt_SetFiniteSet$5(v0$67 : BigInt, v1$68 : BigInt, v2$18 : BigInt, v3$1 : BigInt, v4$0 : BigInt): Set[BigInt] = Set[BigInt](v0$67, v4$0, v2$18, v3$1, v1$68)
  
  @production(28)
  @tag("top")
  def pBigInt_SetSetUnion$0(v0$68 : Set[BigInt], v1$69 : Set[BigInt]): Set[BigInt] = v0$68 ++ v1$69
  
  @production(16)
  @tag("top")
  def pBigInt_SetVariable$0(): Set[BigInt] = variable[Set[BigInt]]
  
  @production(2)
  @tag("top")
  def pBigInt_SetSetAdd$0(v0$69 : Set[BigInt], v1$70 : BigInt): Set[BigInt] = v0$69 + v1$70
  
  @production(1)
  @tag("top")
  def pBigInt_SetSetDifference$0(v0$70 : Set[BigInt], v1$71 : Set[BigInt]): Set[BigInt] = v0$70 -- v1$71
  
  @production(1)
  @tag("top")
  def pBigInt_SetSetIntersection$0(v0$71 : Set[BigInt], v1$72 : Set[BigInt]): Set[BigInt] = v0$71 & v1$72
  
  @production(68)
  @tag("top")
  def pRealVariable$0(): Real = variable[Real]
  
  @production(10)
  @tag("top")
  def pRealRealTimes$0(v0$72 : Real, v1$73 : Real): Real = v0$72 * v1$73
  
  @production(9)
  @tag("top")
  def pRealRealPlus$0(v0$73 : Real, v1$74 : Real): Real = v0$73 + v1$74
  
  @production(4)
  @tag("const")
  def pRealFractionalLiteral$0(): Real = Real(0)
  
  @production(2)
  @tag("const")
  def pRealFractionalLiteral$1(): Real = Real(2)
  
  @production(1)
  @tag("const")
  def pRealFractionalLiteral$2(): Real = Real(1)
  
  @production(1)
  @tag("const")
  def pRealFractionalLiteral$3(): Real = Real(4)
  
  @production(2)
  @tag("top")
  def pRealRealDivision$0(v0$74 : Real, v1$75 : Real): Real = v0$74 / v1$75
  
  @production(5)
  @tag("const")
  def pCharCharLiteral$0(): Char = ' '
  
  @production(4)
  @tag("const")
  def pCharCharLiteral$1(): Char = '\n'
  
  @production(3)
  @tag("const")
  def pCharCharLiteral$2(): Char = 'a'
  
  @production(3)
  @tag("const")
  def pCharCharLiteral$3(): Char = '-'
  
  @production(3)
  @tag("const")
  def pCharCharLiteral$4(): Char = '2'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$5(): Char = 'e'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$6(): Char = '8'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$7(): Char = '4'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$8(): Char = '9'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$9(): Char = '5'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$10(): Char = '6'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$11(): Char = '1'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$12(): Char = '0'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$13(): Char = '7'
  
  @production(2)
  @tag("const")
  def pCharCharLiteral$14(): Char = '3'
  
  @production(1)
  @tag("const")
  def pCharCharLiteral$15(): Char = 's'
  
  @production(1)
  @tag("const")
  def pCharCharLiteral$16(): Char = 't'
  
  @production(1)
  @tag("const")
  def pCharCharLiteral$17(): Char = 'u'
  
  @production(1)
  @tag("const")
  def pCharCharLiteral$18(): Char = 'f'
  
  @production(1)
  @tag("const")
  def pCharCharLiteral$19(): Char = 'l'
  
  @production(1)
  @tag("const")
  def pCharCharLiteral$20(): Char = 'r'
  
  @production(12)
  @tag("top")
  def pCharVariable$0(): Char = variable[Char]
  
  @production(26)
  @tag("top")
  def pTP$0_OptionVariable$0[TP$0](): Option[TP$0] = variable[Option[TP$0]]
  
  @production(6)
  @tag("top")
  def pTP$0_OptionSome[TP$0](v$427 : TP$0): Option[TP$0] = Some[TP$0](v$427)
  
  @production(9)
  @tag("top")
  def pTP$0_OptionNone[TP$0](): Option[TP$0] = None[TP$0]()
  
  @production(1)
  @tag("ite")
  def pTP$0_OptionIfExpr$0[TP$0](v0$75 : Boolean, v1$76 : Option[TP$0], v2$19 : Option[TP$0]): Option[TP$0] = if (v0$75) {
    v1$76
  } else {
    v2$19
  }
  
  @production(18)
  @tag("top")
  def pChar_ListVariable$0(): List[Char] = variable[List[Char]]
  
  @production(3)
  @tag("top")
  def pChar_ListCons(h$786 : Char, t$1782 : List[Char]): List[Char] = Cons[Char](h$786, t$1782)
  
  @production(4)
  @tag("top")
  def pChar_ListNil(): List[Char] = Nil[Char]()
  
  @production(1)
  @tag("ite")
  def pChar_ListIfExpr$0(v0$76 : Boolean, v1$77 : List[Char], v2$20 : List[Char]): List[Char] = if (v0$76) {
    v1$77
  } else {
    v2$20
  }
  
  @production(14)
  @tag("top")
  def pBigInt_OptionVariable$0(): Option[BigInt] = variable[Option[BigInt]]
  
  @production(3)
  @tag("top")
  def pBigInt_OptionSome(v$429 : BigInt): Option[BigInt] = Some[BigInt](v$429)
  
  @production(4)
  @tag("top")
  def pBigInt_OptionNone(): Option[BigInt] = None[BigInt]()
  
  @production(2)
  @tag("ite")
  def pBigInt_OptionIfExpr$0(v0$77 : Boolean, v1$78 : Option[BigInt], v2$21 : Option[BigInt]): Option[BigInt] = if (v0$77) {
    v1$78
  } else {
    v2$21
  }
  
  @production(3)
  @tag("top")
  def pInt_ListCons(h$787 : Int, t$1783 : List[Int]): List[Int] = Cons[Int](h$787, t$1783)
  
  @production(2)
  @tag("top")
  def pInt_ListNil(): List[Int] = Nil[Int]()
  
  @production(4)
  @tag("top")
  def pInt_ListVariable$0(): List[Int] = variable[List[Int]]
  
  @production(1)
  @tag("ite")
  def pInt_ListIfExpr$0(v0$78 : Boolean, v1$79 : List[Int], v2$22 : List[Int]): List[Int] = if (v0$78) {
    v1$79
  } else {
    v2$22
  }
  
  @production(7)
  @tag("top")
  def pBoolean_OptionSome(v$430 : Boolean): Option[Boolean] = Some[Boolean](v$430)
  
  @production(3)
  @tag("top")
  def pBoolean_OptionNone(): Option[Boolean] = None[Boolean]()
  
  @production(2)
  @tag("ite")
  def pBoolean_OptionIfExpr$0(v0$79 : Boolean, v1$80 : Option[Boolean], v2$23 : Option[Boolean]): Option[Boolean] = if (v0$79) {
    v1$80
  } else {
    v2$23
  }
  
  @production(2)
  @tag("top")
  def pInt_OptionSome(v$431 : Int): Option[Int] = Some[Int](v$431)
  
  @production(2)
  @tag("top")
  def pInt_OptionNone(): Option[Int] = None[Int]()
  
  @production(4)
  @tag("top")
  def pInt_OptionVariable$0(): Option[Int] = variable[Option[Int]]

  // FIXME: Manually added
  @production(1)
  def mkT2[T1, T2](e1: T1, e2: T2): (T1, T2) = (e1, e2)

  @production(1)
  def mkT3[T1, T2, T3](e1: T1, e2: T2, e3: T3): (T1, T2, T3) = (e1, e2, e3)

  @production(1)
  def mkT4[T1, T2, T3, T4](e1: T1, e2: T2, e3: T3, e4: T4): (T1, T2, T3, T4) = (e1, e2, e3, e4)




}

