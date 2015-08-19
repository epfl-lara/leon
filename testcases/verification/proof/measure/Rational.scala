/* Copyright 2009-2015 EPFL, Lausanne */

package leon.testcases.verification.proof.measure

import leon.proof._
import leon.lang._
import scala.language.implicitConversions

object Rational {
  implicit def bigInt2Rational(x: BigInt) = Rational(x, 1)
}

/**
 * Represents rational number 'n / d', where 'n' is the numerator and
 * 'd' the denominator.
 */
case class Rational (n: BigInt, d: BigInt) {

  def +(that: Rational): Rational = {
    require(isRational && that.isRational)
    Rational(n * that.d + that.n * d, d * that.d)
  } ensuring { res =>
    res.isRational &&
    ((this.isPositive == that.isPositive) ==>
      (res.isPositive == this.isPositive))
  }

  def -(that: Rational): Rational = {
    require(isRational && that.isRational)
    Rational(n * that.d - that.n * d, d * that.d)
  } ensuring { res =>
    res.isRational &&
    ((this.isPositive != that.isPositive) ==>
      (res.isPositive == this.isPositive))
  }

  def *(that: Rational): Rational = {
    require(isRational && that.isRational)
    Rational(n * that.n, d * that.d)
  } ensuring { res =>
    res.isRational &&
    (res.isNonZero == (this.isNonZero && that.isNonZero)) &&
    (res.isPositive == (!res.isNonZero || this.isPositive == that.isPositive))
  }

  def /(that: Rational): Rational = {
    require(isRational && that.isRational && that.isNonZero)
    Rational(n * that.d, d * that.n)
  } ensuring { res =>
    res.isRational &&
    (res.isNonZero == this.isNonZero) &&
    (res.isPositive == (!res.isNonZero || this.isPositive == that.isPositive))
  }

  def <=(that: Rational): Boolean = {
    require(isRational && that.isRational)
    if (that.d * d > 0)
      n * that.d <= d * that.n
    else
      n * that.d >= d * that.n
  }

  def <(that: Rational): Boolean = {
    require(isRational && that.isRational)
    if (that.d * d > 0)
      n * that.d < d * that.n
    else
      n * that.d > d * that.n
  }

  def >=(that: Rational): Boolean = {
    require(isRational && that.isRational)
    that <= this
  }

  def >(that: Rational): Boolean = {
    require(isRational && that.isRational)
    that < this
  }

  // Equivalence of two rationals, true if they represent the same real number
  def ~(that: Rational): Boolean = {
    require(isRational && that.isRational)
    n * that.d == that.n * d
  }

  def isRational = d != 0
  def isPositive = isRational && (n * d >= 0)
  def isNonZero  = isRational && (n != 0)
}

object RationalSpecs {

  def equivalenceOverAddition(a1: Rational, a2: Rational, b1: Rational, b2: Rational): Boolean = {
    require(
      a1.isRational && a2.isRational && b1.isRational && b2.isRational &&
        a1 ~ a2 && b1 ~ b2
    )

    (a1 + b1) ~ (a2 + b2)
  }.holds

  def equivalenceOverSubstraction(a1: Rational, a2: Rational, b1: Rational, b2: Rational): Boolean = {
    require(
      a1.isRational && a2.isRational && b1.isRational && b2.isRational &&
        a1 ~ a2 && b1 ~ b2
    )

    (a1 - b1) ~ (a2 - b2)
  }.holds

  def equivalenceOverMultiplication(a1: Rational, a2: Rational, b1: Rational, b2: Rational): Boolean = {
    require(
      a1.isRational && a2.isRational && b1.isRational && b2.isRational &&
        a1 ~ a2 && b1 ~ b2
    )

    (a1 * b1) ~ (a2 * b2)
  }.holds

  def equivalenceOverDivision(a1: Rational, a2: Rational, b1: Rational, b2: Rational): Boolean = {
    require(
      a1.isRational && a2.isRational && b1.isRational && b2.isRational &&
        a1 ~ a2 && b1 ~ b2 &&
        b1.isNonZero // in addition to the usual requirements
    )

    (a1 / b1) ~ (a2 / b2)
  }.holds

  def additionPreservesOrdering(a: Rational, b: Rational, c: Rational): Boolean = {
    require(a.isRational && b.isRational && c.isRational)

    (a <= b) ==> (a + c <= b + c) &&
    (a <= b) ==> (c + a <= c + b)
  }.holds

  def orderingTransitivity(a: Rational, b: Rational, c: Rational): Boolean = {
    require(a.isRational && b.isRational && c.isRational)

    ((a < b) && (b < c)) ==> (a < c) &&
    (((a <= b) && (b <= c)) ==> (a <= c))
  }.holds

  def orderingAntisymmetry(a: Rational, b: Rational): Boolean = {
    require(a.isRational && b.isRational)

    (a <= b && b <= a) ==> a ~ b
  }.holds

  def orderingReflexivity(a: Rational): Boolean = {
    require(a.isRational)

    a <= a
  }.holds

  def orderingIrreflexivity(a: Rational): Boolean = {
    require(a.isRational)

    !(a < a)
  }.holds

  def orderingExtra(a: Rational, b: Rational): Boolean = {
    require(a.isRational && b.isRational)

    ((a < b) == !(b <= a)) &&
    ((a < b) == (a <= b && !(a ~ b)))
  }.holds

  def plusAssoc(a: Rational, b: Rational, c: Rational): Boolean = {
    require(a.isRational && b.isRational && c.isRational)

    (a + b) + c == a + (b + c)
  }.holds

  def plusComm(a: Rational, b: Rational): Boolean = {
    require(a.isRational && b.isRational)

    a + b == b + a
  }.holds
}

