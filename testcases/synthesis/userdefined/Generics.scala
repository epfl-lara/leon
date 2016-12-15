import leon.lang._
import leon.lang.synthesis._
import leon.annotation.grammar._
import leon.grammar._

import Grammar1._

object Grammar1 {

  abstract class List[T] {
    def size: BigInt = {
      this match {
        case Cons(h, t) => t.size + 1
        case Nil() => BigInt(0)
      }
    } ensuring { _ >= 0 }
  }

  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  @label
  implicit class NonZero(val v: BigInt)

  @production
  implicit def nonzerotoint(x: NonZero): BigInt = x.v


  @production
  @tag("commut")
  def times(x: NonZero, y: NonZero): NonZero = {
    x * y
  }

  @production
  @tag("commut")
  def plus(x: NonZero, y: NonZero): NonZero = {
    x + y
  }

  //@production
  //def term0(): BigInt = 0

  //@production
  //def term2(): NonZero = NonZero(2)

  @production
  def size[T](l: List[T]): NonZero = {
    l.size
  }

  @production
  def nil[T]: List[T] = Nil[T]()

  @production
  def cons[T](h: T, t: List[T]): List[T] = Cons(h, t)

  //@production
  //def listPm[T](l: List[T], f: (T, List[T]) => BigInt, y: BigInt): BigInt = {
  //  l match {
  //    case Cons(h,t) =>
  //      f(h, t)
  //    case Nil() =>
  //      y
  //  }
  //}

  @production
  def thisdoesntmatter[A]: A = variable[A]
}

object Test1 {

  //def nonEmptyList[B](x: B): List[B] = {
  //  ???[List[B]]
  //} ensuring { r => r.size > 0 }

  //def size1[B](x: List[B]): BigInt = {
  //  require(x.size > 1)
  //  ???[BigInt]
  //} ensuring { r => r > 0 }

  def size2[B](x: List[B]): BigInt = {
    ???[BigInt]
  } ensuring { r => r > 0 }

  //def find4Times(x: BigInt, y: BigInt): BigInt = {
  //  ???[BigInt]
  //} ensuring { res => res >= x*4 && res <= 4*x }

}
