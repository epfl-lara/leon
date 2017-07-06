package leon
package grammar
import leon.collection._
import leon.collection.List._
import leon.collection.ListOps._
import leon.collection.ListSpecs._
import leon.lang.Set._
import leon.lang._
import leon.lang._
import leon.math._
import annotation.grammar._
import heap.Heaps._

object GrammarHeap {
  @production(245)
  @tag("top")
  def pBigIntVariable(): BigInt = variable[BigInt]
  
  @production(86)
  @tag("0")
  def pBigIntInfiniteIntegerLiteral$0(): BigInt = BigInt(0)
  
  @production(53)
  @tag("1")
  def pBigIntInfiniteIntegerLiteral$1(): BigInt = BigInt(1)
  
  @production(5)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$2(): BigInt = BigInt(-1)
  
  @production(4)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$3(): BigInt = BigInt(10)
  
  @production(3)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$4(): BigInt = BigInt(2)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$5(): BigInt = BigInt(5)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$6(): BigInt = BigInt(6)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$7(): BigInt = BigInt(9)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$8(): BigInt = BigInt(7)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$9(): BigInt = BigInt(3)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$10(): BigInt = BigInt(8)
  
  @production(1)
  @tag("const")
  def pBigIntInfiniteIntegerLiteral$11(): BigInt = BigInt(4)
  
  @production(38)
  @tag("minus")
  def pBigIntMinus(v0 : BigInt, v1 : BigInt): BigInt = v0 - v1
  
  @production(37)
  @tag("plus")
  def pBigIntPlus(v0 : BigInt, v1 : BigInt): BigInt = v0 + v1
  
  @production(28)
  @tag("times")
  def pBigIntTimes(v0 : BigInt, v1 : BigInt): BigInt = v0 * v1
  
  @production(11)
  @tag("top")
  def pBigIntUMinus(v0 : BigInt): BigInt = -v0
  
  @production(2)
  @tag("div")
  def pBigIntDivision(v0 : BigInt, v1 : BigInt): BigInt = v0 / v1
  
  @production(2)
  @tag("mod")
  def pBigIntModulo(v0 : BigInt, v1 : BigInt): BigInt = v0 mod v1
  
  @production(1)
  @tag("top")
  def pBigIntRemainder(v0 : BigInt, v1 : BigInt): BigInt = v0 % v1
  
  @production(363)
  @tag("top")
  def pTP$0Variable[TP$0](): TP$0 = variable[TP$0]
  
  @production(68)
  @tag("top")
  def pHeap$0Variable(): Heap = variable[Heap]
  
  @production(3)
  @tag("top")
  def pHeap$0Node(value : BigInt, left : Heap, right : Heap): Heap = Node(value, left, right)
  
  @production(2)
  @tag("top")
  def pHeap$0Leaf(): Heap = Leaf()
  
  @production(11)
  @tag("top")
  def pBigInt_ListVariable(): List[BigInt] = variable[List[BigInt]]
  
  @production(4)
  @tag("top")
  def pBigInt_ListCons(h : BigInt, t : List[BigInt]): List[BigInt] = Cons[BigInt](h, t)
  
  @production(3)
  @tag("top")
  def pBigInt_ListNil(): List[BigInt] = Nil[BigInt]()
  
  @production(4)
  @tag("top")
  def pBigInt_SetSetUnion(v0 : Set[BigInt], v1 : Set[BigInt]): Set[BigInt] = v0 ++ v1
  
  @production(2)
  @tag("top")
  def pBigInt_SetFiniteSet(v0 : BigInt): Set[BigInt] = Set[BigInt](v0)
  
  @production(1)
  @tag("top")
  def pBigInt_SetFiniteSet(): Set[BigInt] = Set[BigInt]()
  
  @production(1)
  @tag("top")
  def pBigInt_OptionSome(v : BigInt): Option[BigInt] = Some[BigInt](v)
  
  @production(1)
  @tag("top")
  def pBigInt_OptionNone(): Option[BigInt] = None[BigInt]()
  
  @tag("top")
  @production(1)
  def fd$0(v0 : List[BigInt]): BigInt = v0.size
  
  @tag("top")
  @production(1)
  def fd$1(v0 : BigInt, v1 : BigInt): List[BigInt] = range(v0, v1)
  
  @tag("top")
  @production(1)
  def fd$2(v0 : List[BigInt]): List[BigInt] = sorted(v0)
}

