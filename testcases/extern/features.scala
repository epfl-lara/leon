package testextern

import leon.lang._
import leon.annotation._
import leon.lang.synthesis._
import leon.collection._

object ExternTest {
  // All types 1
  def test1() = {
    allTypes1(false, (1,2), ExternFoo(12), Bar(false))
  }

  // All types 2
  def test2() = {
    allTypes2(Set(1,2,3), Map(1->2))
  }

  // External function calling back
  def test3() = {
    testCallBack(51);
  }

  // External method
  def test4() = {
    Test(12).bar(21)
  }

  // Generics
  def test5() = {
    id(List[BigInt](1,2,3)).tail.head == 2
  }

  // Name encoding
  def test6() = {
    +*/!(1,2)
  }

  // Unit1
  def test7() = {
    testUnit(1, (), ((), 3))
  }


  def leonFun(a: BigInt): BigInt = {
    choose((x: BigInt) => x > a && x <= a+1)
  }



  // External functions

  @extern
  def testCallBack(a: BigInt): BigInt = {
    val f = new scala.collection.mutable.ArrayBuffer[BigInt]()
    leonFun(a+1)
  }

  @extern
  def +*/!(a: Int, b: BigInt): BigInt = {
    println("asd")
    b+b
  }

  @extern
  def allTypes1(a: Boolean, b: (BigInt, BigInt), c: ExternFoo, d: Bar): (Boolean, (BigInt, BigInt), ExternFoo, Bar) = {
    println("asd")
    (a,b,c,d)
  }

  @extern
  def allTypes2(s: Set[Int], m: Map[Int, Int]): (Set[Int], Map[Int, Int]) = {
    println("asd")
    (s,m)
  }

  @extern
  def id[T](a: T): T = {
    println("asd")
    a
  }

  @extern
  def testUnit(a: Int, b: Unit, c: (Unit, Int)): Unit = {
    println("asd")
    b
  }

  case class Test(a: Int) {
    @extern
    def bar(b: BigInt): BigInt = {
      println("asd")
      b*4+a
    }
  }

  case class Bar(b: Boolean);
}

case class ExternFoo(a: BigInt) {
  def leonMethod(z: Int): Int = z
}
