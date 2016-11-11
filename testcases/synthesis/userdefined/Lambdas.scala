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


  @production
  def patmat[A,B](x: List[A], consCase: (A, List[A]) => B, nilCase: B): B = {
    x match {
      case Cons(h,t) => consCase(h,t)
      case Nil() => nilCase
    }
  }

  @production
  def tr: Boolean = true

  @production
  def fa: Boolean = false

  @production
  def nil[T]: List[T] = Nil[T]()

  @production
  def isNil[T](x: List[T]): Boolean = x == Nil[T]()

  @production
  def cons[T](h: T, t: List[T]): List[T] = Cons(h, t)

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

  def matchUse(x: List[BigInt]): Boolean= {
    ???[Boolean]
  } ensuring { r => eq(r, (x.size == 1)) }


  /*
  def closures(x: List[BigInt]): ((List[BigInt], List[BigInt]) => Boolean) = {
    ???[((List[BigInt], List[BigInt]) => Boolean)]
  } ensuring { f => f(x, x) == true }
  */

  def eq(a: Boolean, b: Boolean) = a == b

  //def find4Times(x: BigInt, y: BigInt): BigInt = {
  //  ???[BigInt]
  //} ensuring { res => res >= x*4 && res <= 4*x }

}
