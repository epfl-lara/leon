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
  @production(1787)
  @tag("and")
  def pBooleanAnd(v0 : Boolean, v1 : Boolean): Boolean = v0 && v1
  
  @production(1108)
  @tag("top")
  def pBooleanVariable(): Boolean = variable[Boolean]
  
  @production(7)
  @tag("top")
  def pBooleanLessEquals(v0 : Real, v1 : Real): Boolean = v0 <= v1
  
  @production(349)
  @tag("top")
  def pBooleanLessEquals(v0 : BigInt, v1 : BigInt): Boolean = v0 <= v1
  
  @production(597)
  @tag("top")
  def pBooleanLessEquals(v0 : Int, v1 : Int): Boolean = v0 <= v1
  
  @production(9)
  @tag("equals")
  def pBooleanEquals(v0 : Real, v1 : Real): Boolean = v0 == v1
  
  @production(3)
  @tag("equals")
  def pBooleanEquals(v0 : Option[Boolean], v1 : Option[Boolean]): Boolean = v0 == v1
  
  @production(18)
  @tag("equals")
  def pBooleanEquals(v0 : List[BigInt], v1 : List[BigInt]): Boolean = v0 == v1
  
  @production(4)
  @tag("equals")
  def pBooleanEquals(v0 : Char, v1 : Char): Boolean = v0 == v1
  
  @production(350)
  @tag("equals")
  def pBooleanEquals(v0 : BigInt, v1 : BigInt): Boolean = v0 == v1
  
  @production(24)
  @tag("equals")
  def pBooleanEquals[TP$0](v0 : Set[TP$0], v1 : Set[TP$0]): Boolean = v0 == v1
  
  @production(75)
  @tag("equals")
  def pBooleanEquals(v0 : Set[Int], v1 : Set[Int]): Boolean = v0 == v1
  
  @production(2)
  @tag("equals")
  def pBooleanEquals(v0 : Option[BigInt], v1 : Option[BigInt]): Boolean = v0 == v1
  
  @production(230)
  @tag("equals")
  def pBooleanEquals(v0 : Int, v1 : Int): Boolean = v0 == v1
  
  @production(24)
  @tag("equals")
  def pBooleanEquals(v0 : Set[BigInt], v1 : Set[BigInt]): Boolean = v0 == v1
  
  @production(43)
  @tag("equals")
  def pBooleanEquals[TP$0](v0 : List[TP$0], v1 : List[TP$0]): Boolean = v0 == v1
  
  @production(2)
  @tag("equals")
  def pBooleanEquals(v0 : List[Char], v1 : List[Char]): Boolean = v0 == v1
  
  @production(1)
  @tag("equals")
  def pBooleanEquals(v0 : Unit, v1 : Unit): Boolean = v0 == v1
  
  @production(82)
  @tag("equals")
  def pBooleanEquals(v0 : Boolean, v1 : Boolean): Boolean = v0 == v1
  
  @production(24)
  @tag("equals")
  def pBooleanEquals[TP$0](v0 : TP$0, v1 : TP$0): Boolean = v0 == v1
  
  @production(478)
  @tag("booleanC")
  def pBooleanBooleanLiteral$0(): Boolean = true
  
  @production(221)
  @tag("booleanC")
  def pBooleanBooleanLiteral$1(): Boolean = false
  
  @production(9)
  @tag("top")
  def pBooleanLessThan(v0 : Real, v1 : Real): Boolean = v0 < v1
  
  @production(245)
  @tag("top")
  def pBooleanLessThan(v0 : BigInt, v1 : BigInt): Boolean = v0 < v1
  
  @production(436)
  @tag("top")
  def pBooleanLessThan(v0 : Int, v1 : Int): Boolean = v0 < v1
  
  @production(487)
  @tag("not")
  def pBooleanNot(v0 : Boolean): Boolean = !v0
  
  @production(154)
  @tag("ite")
  def pBooleanIfExpr(v0 : Boolean, v1 : Boolean, v2 : Boolean): Boolean = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(139)
  @tag("or")
  def pBooleanOr(v0 : Boolean, v1 : Boolean): Boolean = v0 || v1
  
  @production(16)
  @tag("top")
  def pBooleanElementOfSet[TP$0](v0 : TP$0, v1 : Set[TP$0]): Boolean = v1.contains(v0)
  
  @production(23)
  @tag("top")
  def pBooleanElementOfSet(v0 : BigInt, v1 : Set[BigInt]): Boolean = v1.contains(v0)
  
  @production(25)
  @tag("top")
  def pBooleanElementOfSet(v0 : Int, v1 : Set[Int]): Boolean = v1.contains(v0)
  
  @production(50)
  @tag("top")
  def pBooleanImplies(v0 : Boolean, v1 : Boolean): Boolean = v0 ==> v1
  
  @production(3)
  @tag("top")
  def pBooleanSubsetOf(v0 : Set[Int], v1 : Set[Int]): Boolean = v0.subsetOf(v1)
  
  @production(9)
  @tag("top")
  def pBooleanSubsetOf[TP$0](v0 : Set[TP$0], v1 : Set[TP$0]): Boolean = v0.subsetOf(v1)
  
  @production(3487)
  @tag("top")
  def pIntVariable(): Int = variable[Int]
  
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
  
  @production(299)
  @tag("plus")
  def pIntBVPlus(v0 : Int, v1 : Int): Int = v0 + v1
  
  @production(104)
  @tag("minus")
  def pIntBVMinus(v0 : Int, v1 : Int): Int = v0 - v1
  
  @production(31)
  @tag("ite")
  def pIntIfExpr(v0 : Boolean, v1 : Int, v2 : Int): Int = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(20)
  @tag("times")
  def pIntBVTimes(v0 : Int, v1 : Int): Int = v0 * v1
  
  @production(11)
  @tag("top")
  def pIntBVDivision(v0 : Int, v1 : Int): Int = v0 / v1
  
  @production(10)
  @tag("top")
  def pIntBVAShiftRight(v0 : Int, v1 : Int): Int = v0 >> v1
  
  @production(6)
  @tag("top")
  def pIntBVAnd(v0 : Int, v1 : Int): Int = v0 & v1
  
  @production(5)
  @tag("top")
  def pIntBVXOr(v0 : Int, v1 : Int): Int = v0 ^ v1
  
  @production(4)
  @tag("top")
  def pIntBVShiftLeft(v0 : Int, v1 : Int): Int = v0 << v1
  
  @production(3)
  @tag("top")
  def pIntBVLShiftRight(v0 : Int, v1 : Int): Int = v0 >>> v1
  
  @production(3)
  @tag("top")
  def pIntBVOr(v0 : Int, v1 : Int): Int = v0 | v1
  
  @production(3)
  @tag("top")
  def pIntBVRemainder(v0 : Int, v1 : Int): Int = v0 % v1
  
  @production(2)
  @tag("top")
  def pIntBVUMinus(v0 : Int): Int = -v0
  
  @production(2683)
  @tag("top")
  def pBigIntVariable(): BigInt = variable[BigInt]
  
  @production(566)
  @tag("0")
  def pBigIntInfiniteIntegerLiteral$0(): BigInt = BigInt(0)
  
  @production(379)
  @tag("1")
  def pBigIntInfiniteIntegerLiteral$1(): BigInt = BigInt(1)
  
  @production(97)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$2(): BigInt = BigInt(2)
  
  @production(23)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$3(): BigInt = BigInt(10)
  
  @production(14)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$4(): BigInt = BigInt(5)
  
  @production(12)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$5(): BigInt = BigInt(60)
  
  @production(11)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$6(): BigInt = BigInt(-1)
  
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
  
  @production(283)
  @tag("minus")
  def pBigIntMinus(v0 : BigInt, v1 : BigInt): BigInt = v0 - v1
  
  @production(216)
  @tag("plus")
  def pBigIntPlus(v0 : BigInt, v1 : BigInt): BigInt = v0 + v1
  
  @production(143)
  @tag("times")
  def pBigIntTimes(v0 : BigInt, v1 : BigInt): BigInt = v0 * v1
  
  @production(46)
  @tag("ite")
  def pBigIntIfExpr(v0 : Boolean, v1 : BigInt, v2 : BigInt): BigInt = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(34)
  @tag("div")
  def pBigIntDivision(v0 : BigInt, v1 : BigInt): BigInt = v0 / v1
  
  @production(28)
  @tag("top")
  def pBigIntUMinus(v0 : BigInt): BigInt = -v0
  
  @production(19)
  @tag("top")
  def pBigIntRemainder(v0 : BigInt, v1 : BigInt): BigInt = v0 % v1
  
  @production(2)
  @tag("mod")
  def pBigIntModulo(v0 : BigInt, v1 : BigInt): BigInt = v0 mod v1
  
  @production(883)
  @tag("top")
  def pTP$0_ListVariable[TP$0](): List[TP$0] = variable[List[TP$0]]
  
  @production(62)
  @tag("top")
  def pTP$0_ListCons[TP$0](h : TP$0, t : List[TP$0]): List[TP$0] = Cons[TP$0](h, t)
  
  @production(82)
  @tag("top")
  def pTP$0_ListNil[TP$0](): List[TP$0] = Nil[TP$0]()
  
  @production(16)
  @tag("ite")
  def pTP$0_ListIfExpr[TP$0](v0 : Boolean, v1 : List[TP$0], v2 : List[TP$0]): List[TP$0] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(629)
  @tag("top")
  def pTP$0Variable[TP$0](): TP$0 = variable[TP$0]
  
  @production(4)
  @tag("ite")
  def pTP$0IfExpr[TP$0](v0 : Boolean, v1 : TP$0, v2 : TP$0): TP$0 = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(276)
  @tag("top")
  def pBigInt_ListVariable(): List[BigInt] = variable[List[BigInt]]
  
  @production(43)
  @tag("top")
  def pBigInt_ListCons(h : BigInt, t : List[BigInt]): List[BigInt] = Cons[BigInt](h, t)
  
  @production(32)
  @tag("top")
  def pBigInt_ListNil(): List[BigInt] = Nil[BigInt]()
  
  @production(5)
  @tag("ite")
  def pBigInt_ListIfExpr(v0 : Boolean, v1 : List[BigInt], v2 : List[BigInt]): List[BigInt] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(215)
  @tag("const")
  def pUnitUnitLiteral$0(): Unit = ()
  
  @production(113)
  @tag("top")
  def pUnitVariable(): Unit = variable[Unit]
  
  @production(152)
  @tag("top")
  def pTP$0_SetVariable[TP$0](): Set[TP$0] = variable[Set[TP$0]]
  
  @production(35)
  @tag("top")
  def pTP$0_SetSetUnion[TP$0](v0 : Set[TP$0], v1 : Set[TP$0]): Set[TP$0] = v0 ++ v1
  
  @production(13)
  @tag("top")
  def pTP$0_SetFiniteSet[TP$0](v0 : TP$0): Set[TP$0] = Set[TP$0](v0)
  
  @production(12)
  @tag("top")
  def pTP$0_SetFiniteSet[TP$0](): Set[TP$0] = Set[TP$0]()
  
  @production(3)
  @tag("ite")
  def pTP$0_SetIfExpr[TP$0](v0 : Boolean, v1 : Set[TP$0], v2 : Set[TP$0]): Set[TP$0] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(3)
  @tag("top")
  def pTP$0_SetSetDifference[TP$0](v0 : Set[TP$0], v1 : Set[TP$0]): Set[TP$0] = v0 -- v1
  
  @production(2)
  @tag("top")
  def pTP$0_SetSetIntersection[TP$0](v0 : Set[TP$0], v1 : Set[TP$0]): Set[TP$0] = v0 & v1
  
  @production(108)
  @tag("top")
  def pInt_SetSetUnion(v0 : Set[Int], v1 : Set[Int]): Set[Int] = v0 ++ v1
  
  @production(53)
  @tag("top")
  def pInt_SetFiniteSet(v0 : Int): Set[Int] = Set[Int](v0)
  
  @production(3)
  @tag("top")
  def pInt_SetFiniteSet(): Set[Int] = Set[Int]()
  
  @production(44)
  @tag("top")
  def pInt_SetVariable(): Set[Int] = variable[Set[Int]]
  
  @production(1)
  @tag("top")
  def pInt_SetSetDifference(v0 : Set[Int], v1 : Set[Int]): Set[Int] = v0 -- v1
  
  @production(2)
  @tag("top")
  def pBigInt_SetFiniteSet(v0 : BigInt, v1 : BigInt, v2 : BigInt): Set[BigInt] = Set[BigInt](v0, v1, v2)
  
  @production(2)
  @tag("top")
  def pBigInt_SetFiniteSet(v0 : BigInt, v1 : BigInt): Set[BigInt] = Set[BigInt](v0, v1)
  
  @production(22)
  @tag("top")
  def pBigInt_SetFiniteSet(v0 : BigInt): Set[BigInt] = Set[BigInt](v0)
  
  @production(3)
  @tag("top")
  def pBigInt_SetFiniteSet(): Set[BigInt] = Set[BigInt]()
  
  @production(3)
  @tag("top")
  def pBigInt_SetFiniteSet(v0 : BigInt, v1 : BigInt, v2 : BigInt, v3 : BigInt): Set[BigInt] = Set[BigInt](v0, v1, v2, v3)
  
  @production(3)
  @tag("top")
  def pBigInt_SetFiniteSet(v0 : BigInt, v1 : BigInt, v2 : BigInt, v3 : BigInt, v4 : BigInt): Set[BigInt] = Set[BigInt](v1, v3, v4, v2, v0)
  
  @production(28)
  @tag("top")
  def pBigInt_SetSetUnion(v0 : Set[BigInt], v1 : Set[BigInt]): Set[BigInt] = v0 ++ v1
  
  @production(16)
  @tag("top")
  def pBigInt_SetVariable(): Set[BigInt] = variable[Set[BigInt]]
  
  @production(2)
  @tag("top")
  def pBigInt_SetSetAdd(v0 : Set[BigInt], v1 : BigInt): Set[BigInt] = v0 + v1
  
  @production(1)
  @tag("top")
  def pBigInt_SetSetDifference(v0 : Set[BigInt], v1 : Set[BigInt]): Set[BigInt] = v0 -- v1
  
  @production(1)
  @tag("top")
  def pBigInt_SetSetIntersection(v0 : Set[BigInt], v1 : Set[BigInt]): Set[BigInt] = v0 & v1
  
  @production(68)
  @tag("top")
  def pRealVariable(): Real = variable[Real]
  
  @production(10)
  @tag("top")
  def pRealRealTimes(v0 : Real, v1 : Real): Real = v0 * v1
  
  @production(9)
  @tag("top")
  def pRealRealPlus(v0 : Real, v1 : Real): Real = v0 + v1
  
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
  def pRealRealDivision(v0 : Real, v1 : Real): Real = v0 / v1
  
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
  def pCharVariable(): Char = variable[Char]
  
  @production(26)
  @tag("top")
  def pTP$0_OptionVariable[TP$0](): Option[TP$0] = variable[Option[TP$0]]
  
  @production(6)
  @tag("top")
  def pTP$0_OptionSome[TP$0](v : TP$0): Option[TP$0] = Some[TP$0](v)
  
  @production(9)
  @tag("top")
  def pTP$0_OptionNone[TP$0](): Option[TP$0] = None[TP$0]()
  
  @production(1)
  @tag("ite")
  def pTP$0_OptionIfExpr[TP$0](v0 : Boolean, v1 : Option[TP$0], v2 : Option[TP$0]): Option[TP$0] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(18)
  @tag("top")
  def pChar_ListVariable(): List[Char] = variable[List[Char]]
  
  @production(3)
  @tag("top")
  def pChar_ListCons(h : Char, t : List[Char]): List[Char] = Cons[Char](h, t)
  
  @production(4)
  @tag("top")
  def pChar_ListNil(): List[Char] = Nil[Char]()
  
  @production(1)
  @tag("ite")
  def pChar_ListIfExpr(v0 : Boolean, v1 : List[Char], v2 : List[Char]): List[Char] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(14)
  @tag("top")
  def pBigInt_OptionVariable(): Option[BigInt] = variable[Option[BigInt]]
  
  @production(3)
  @tag("top")
  def pBigInt_OptionSome(v : BigInt): Option[BigInt] = Some[BigInt](v)
  
  @production(4)
  @tag("top")
  def pBigInt_OptionNone(): Option[BigInt] = None[BigInt]()
  
  @production(2)
  @tag("ite")
  def pBigInt_OptionIfExpr(v0 : Boolean, v1 : Option[BigInt], v2 : Option[BigInt]): Option[BigInt] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(3)
  @tag("top")
  def pInt_ListCons(h : Int, t : List[Int]): List[Int] = Cons[Int](h, t)
  
  @production(2)
  @tag("top")
  def pInt_ListNil(): List[Int] = Nil[Int]()
  
  @production(4)
  @tag("top")
  def pInt_ListVariable(): List[Int] = variable[List[Int]]
  
  @production(1)
  @tag("ite")
  def pInt_ListIfExpr(v0 : Boolean, v1 : List[Int], v2 : List[Int]): List[Int] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(7)
  @tag("top")
  def pBoolean_OptionSome(v : Boolean): Option[Boolean] = Some[Boolean](v)
  
  @production(3)
  @tag("top")
  def pBoolean_OptionNone(): Option[Boolean] = None[Boolean]()
  
  @production(2)
  @tag("ite")
  def pBoolean_OptionIfExpr(v0 : Boolean, v1 : Option[Boolean], v2 : Option[Boolean]): Option[Boolean] = if (v0) {
    v1
  } else {
    v2
  }
  
  @production(2)
  @tag("top")
  def pInt_OptionSome(v : Int): Option[Int] = Some[Int](v)
  
  @production(2)
  @tag("top")
  def pInt_OptionNone(): Option[Int] = None[Int]()
  
  @production(4)
  @tag("top")
  def pInt_OptionVariable(): Option[Int] = variable[Option[Int]]
  
  @tag("top")
  @production(146)
  def fd$1(v0 : List[BigInt]): BigInt = v0.size
  
  @tag("top")
  @production(10)
  def fd$2(v0 : List[BigInt]): BigInt = v0.last
  
  @tag("top")
  @production(6)
  def fd$3[T](v0 : List[T]): BigInt = v0.length
  
  @tag("top")
  @production(4)
  def fd$4(v0 : List[BigInt]): BigInt = v0.head
  
  @tag("top")
  @production(3)
  def fd$5[T](v0 : List[T], v1 : T): BigInt = v0.indexOf(v1)
  
  @tag("top")
  @production(17)
  def fd$6(v0 : List[BigInt]): Boolean = v0.isEmpty
  
  @tag("top")
  @production(7)
  def fd$7(v0 : List[BigInt], v1 : BigInt): Boolean = v0.contains(v1)
  
  @tag("top")
  @production(4)
  def fd$8(v0 : List[BigInt]): Boolean = isSorted(v0)
  
  @tag("top")
  @production(3)
  def fd$9(v0 : List[BigInt]): Boolean = v0.nonEmpty
  
  @tag("top")
  @production(2)
  def fd$10[T](v0 : List[T], v1 : T, v2 : BigInt): Boolean = snocIndex[T](v0, v1, v2)
  
  @tag("top")
  @production(2)
  def fd$11[T](v0 : List[T], v1 : T): Boolean = snocLast[T](v0, v1)
  
  @tag("top")
  @production(2)
  def fd$12[T](v0 : List[T], v1 : T): Boolean = snocIsAppend[T](v0, v1)
  
  @tag("top")
  @production(2)
  def fd$13[T](v0 : List[T], v1 : List[T], v2 : T): Boolean = snocAfterAppend[T](v0, v1, v2)
  
  @tag("top")
  @production(2)
  def fd$14[T](v0 : List[T], v1 : T): Boolean = snocReverse[T](v0, v1)
  
  @tag("top")
  @production(1)
  def fd$15[T](v0 : T, v1 : List[T], v2 : BigInt): Boolean = consIndex[T](v0, v1, v2)
  
  @tag("top")
  @production(1)
  def fd$16[T](v0 : List[T], v1 : BigInt): Boolean = reverseIndex[T](v0, v1)
  
  @tag("top")
  @production(1)
  def fd$17[T](v0 : List[T], v1 : List[T], v2 : BigInt): Boolean = appendIndex[T](v0, v1, v2)
  
  @tag("top")
  @production(1)
  def fd$18[T](v0 : List[T], v1 : List[T], v2 : List[T]): Boolean = appendAssoc[T](v0, v1, v2)
  
  @tag("top")
  @production(1)
  def fd$19[T](v0 : List[T]): Boolean = rightUnitAppend[T](v0)
  
  @tag("top")
  @production(1)
  def fd$20[T](v0 : List[T]): Boolean = reverseReverse[T](v0)
  
  @tag("top")
  @production(1)
  def fd$21[T](v0 : List[T], v1 : List[T]): Boolean = reverseAppend[T](v0, v1)
  
  @tag("top")
  @production(1)
  def fd$22[T](v0 : List[T], v1 : List[T]): Boolean = appendContent[T](v0, v1)
  
  @tag("top")
  @production(1)
  def fd$23[T](v0 : List[T], v1 : List[T], v2 : BigInt, v3 : T): Boolean = appendUpdate[T](v0, v1, v2, v3)
  
  @tag("top")
  @production(1)
  def fd$24[T](v0 : List[T], v1 : List[T], v2 : BigInt): Boolean = appendTakeDrop[T](v0, v1, v2)
  
  @tag("top")
  @production(1)
  def fd$25[T](v0 : List[T], v1 : List[T], v2 : BigInt, v3 : T): Boolean = appendInsert[T](v0, v1, v2, v3)
  
  @tag("top")
  @production(45)
  def fd$26[TP$0](v0 : List[TP$0], v1 : List[TP$0]): List[TP$0] = v0 ++ v1
  
  @tag("top")
  @production(38)
  def fd$27[TP$0](v0 : List[TP$0], v1 : TP$0): List[TP$0] = v1 :: v0
  
  @tag("top")
  @production(37)
  def fd$28[TP$0](v0 : List[TP$0]): List[TP$0] = v0.reverse
  
  @tag("top")
  @production(19)
  def fd$29[TP$0](v0 : List[TP$0], v1 : TP$0): List[TP$0] = v0.:+(v1)
  
  @tag("top")
  @production(8)
  def fd$30[TP$0](v0 : List[TP$0], v1 : BigInt): List[TP$0] = v0.drop(v1)
  
  @tag("top")
  @production(7)
  def fd$31[TP$0](v0 : List[TP$0], v1 : BigInt): List[TP$0] = v0.take(v1)
  
  @tag("top")
  @production(4)
  def fd$32[TP$0](v0 : List[TP$0], v1 : BigInt, v2 : TP$0): List[TP$0] = v0.updated(v1, v2)
  
  @tag("top")
  @production(3)
  def fd$33[TP$0](v0 : List[TP$0], v1 : TP$0): List[TP$0] = v0 - v1
  
  @tag("top")
  @production(3)
  def fd$34[TP$0](v0 : List[TP$0], v1 : BigInt, v2 : TP$0): List[TP$0] = v0.insertAt(v1, v2)
  
  @tag("top")
  @production(2)
  def fd$35[TP$0](v0 : List[TP$0]): List[TP$0] = v0.tail
  
  @tag("top")
  @production(2)
  def fd$36[TP$0](v0 : List[TP$0], v1 : List[TP$0]): List[TP$0] = v0 -- v1
  
  @tag("top")
  @production(2)
  def fd$37[TP$0](v0 : List[TP$0], v1 : List[TP$0]): List[TP$0] = v0.&(v1)
  
  @tag("top")
  @production(2)
  def fd$38[TP$0](v0 : List[TP$0], v1 : BigInt, v2 : TP$0): List[TP$0] = v0.padTo(v1, v2)
  
  @tag("top")
  @production(2)
  def fd$39[TP$0](v0 : List[TP$0]): List[TP$0] = v0.unique
  
  @tag("top")
  @production(1)
  def fd$40[TP$0](v0 : List[TP$0], v1 : TP$0, v2 : TP$0): List[TP$0] = v0.replace(v1, v2)
  
  @tag("top")
  @production(1)
  def fd$41[TP$0](v0 : List[TP$0]): List[TP$0] = v0.init
  
  @tag("top")
  @production(1)
  def fd$42[TP$0](v0 : List[TP$0], v1 : BigInt, v2 : List[TP$0]): List[TP$0] = v0.insertAt(v1, v2)
  
  @tag("top")
  @production(1)
  def fd$43[TP$0](v0 : BigInt, v1 : TP$0): List[TP$0] = fill[TP$0](v0)(v1)
  
  @tag("top")
  @production(83)
  def fd$44[TP$0](v0 : List[TP$0]): Set[TP$0] = v0.content
  
  @tag("top")
  @production(1)
  def fd$45[TP$0](): Set[TP$0] = empty[TP$0]
  
  @tag("top")
  @production(11)
  def fd$46(v0 : List[BigInt], v1 : BigInt): List[BigInt] = v1 :: v0
  
  @tag("top")
  @production(9)
  def fd$47(v0 : List[BigInt], v1 : List[BigInt]): List[BigInt] = v0 ++ v1
  
  @tag("top")
  @production(2)
  def fd$48(v0 : List[BigInt]): List[BigInt] = v0.tail
  
  @tag("top")
  @production(1)
  def fd$49(v0 : BigInt, v1 : BigInt): List[BigInt] = range(v0, v1)
  
  @tag("top")
  @production(1)
  def fd$50(v0 : List[BigInt]): List[BigInt] = sorted(v0)
  
  @tag("top")
  @production(12)
  def fd$51[TP$0](v0 : List[TP$0], v1 : BigInt): TP$0 = v0.apply(v1)
  
  @tag("top")
  @production(6)
  def fd$52[TP$0](v0 : List[TP$0]): TP$0 = v0.head
  
  @tag("top")
  @production(6)
  def fd$53[TP$0](v0 : List[TP$0]): TP$0 = v0.last
  
  @tag("top")
  @production(29)
  def fd$54(): Set[Int] = empty[Int]
  
  @tag("top")
  @production(9)
  def fd$55(): Set[BigInt] = empty[BigInt]
  
  @tag("top")
  @production(8)
  def fd$56(v0 : List[BigInt]): Set[BigInt] = v0.content
  
  @tag("top")
  @production(3)
  def fd$57(v0 : List[BigInt]): Option[BigInt] = v0.headOption
  
  @tag("top")
  @production(1)
  def fd$58[TP$0](v0 : List[TP$0]): Option[TP$0] = v0.lastOption
}
