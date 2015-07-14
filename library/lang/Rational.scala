/* Copyright 2009-2015 EPFL, Lausanne */

package leon.lang

import leon.annotation._

import scala.language.implicitConversions

@library
case class Rational(numerator: BigInt, denominator: BigInt) {

  def +(that: Rational): Rational = {
    require(this.isRational && that.isRational)
    Rational(this.numerator*that.denominator + that.numerator*this.denominator, this.denominator*that.denominator)
  } ensuring(res => res.isRational)

  def -(that: Rational): Rational = {
    require(this.isRational && that.isRational)
    Rational(this.numerator*that.denominator - that.numerator*this.denominator, this.denominator*that.denominator)
  } ensuring(res => res.isRational)

  def unary_- : Rational = {
    require(this.isRational)
    Rational(-this.numerator, this.denominator)
  } ensuring(res => res.isRational)

  def *(that: Rational): Rational = {
    require(this.isRational && that.isRational)
    Rational(this.numerator*that.numerator, this.denominator*that.denominator)
  } ensuring(res => res.isRational)

  def /(that: Rational): Rational = {
    require(this.isRational && that.isRational && that.nonZero)
    val newNumerator = this.numerator*that.denominator
    val newDenominator = this.denominator*that.numerator
    normalize(newNumerator, newDenominator)
  } ensuring(res => res.isRational)

  def reciprocal: Rational = {
    require(this.isRational && this.nonZero)
    normalize(this.denominator, this.numerator)
  } ensuring(res => res.isRational)


  def ~(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    this.numerator*that.denominator == that.numerator*this.denominator
  }

  def <(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    this.numerator*that.denominator < that.numerator*this.denominator
  }

  def <=(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    this.numerator*that.denominator <= that.numerator*this.denominator
  }

  def >(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    this.numerator*that.denominator > that.numerator*this.denominator
  }

  def >=(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    this.numerator*that.denominator >= that.numerator*this.denominator
  }

  def nonZero: Boolean = {
    require(this.isRational)
    numerator != 0
  }

  def isRational: Boolean = denominator > 0

  private def normalize(num: BigInt, den: BigInt): Rational = {
    if(den < 0)
      Rational(-num, -den)
    else
      Rational(num, den)
  }
}

object Rational {

  implicit def bigIntToRat(n: BigInt): Rational = Rational(n, 1)

  def apply(n: BigInt): Rational = Rational(n, 1)
}
