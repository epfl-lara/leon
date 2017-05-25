/* Copyright 2009-2016 EPFL, Lausanne */

package leon.lang

import leon.annotation._
import scala.language.implicitConversions
import scala.Boolean
import scala.Predef.require

@library
@isabelle.typ(name = "Leon_Types.rational")
@isabelle.constructor(name = "Leon_Types.rational.Rational")
case class Rational(numerator: scala.math.BigInt, denominator: scala.math.BigInt) {

  require(this.isRational)

  def +(that: Rational): Rational = {
    Rational(this.numerator*that.denominator + that.numerator*this.denominator, this.denominator*that.denominator)
  }

  def -(that: Rational): Rational = {
    Rational(this.numerator*that.denominator - that.numerator*this.denominator, this.denominator*that.denominator)
  }

  def unary_- : Rational = {
    Rational(-this.numerator, this.denominator)
  }

  def *(that: Rational): Rational = {
    Rational(this.numerator*that.numerator, this.denominator*that.denominator)
  }

  def /(that: Rational): Rational = {
    require(that.nonZero)
    val newNumerator = this.numerator*that.denominator
    val newDenominator = this.denominator*that.numerator
    normalize(newNumerator, newDenominator)
  }

  def reciprocal: Rational = {
    require(this.nonZero)
    normalize(this.denominator, this.numerator)
  }


  def ~(that: Rational): Boolean = {
    this.numerator*that.denominator == that.numerator*this.denominator
  }

  def <(that: Rational): Boolean = {
    this.numerator*that.denominator < that.numerator*this.denominator
  }

  def <=(that: Rational): Boolean = {
    this.numerator*that.denominator <= that.numerator*this.denominator
  }

  def >(that: Rational): Boolean = {
    this.numerator*that.denominator > that.numerator*this.denominator
  }

  def >=(that: Rational): Boolean = {
    this.numerator*that.denominator >= that.numerator*this.denominator
  }

  def nonZero: Boolean = {
    numerator != 0
  }

  private def isRational: Boolean = denominator > 0

  private def normalize(num: scala.math.BigInt, den: scala.math.BigInt): Rational = {
    require(den != 0)
    if(den < 0)
      Rational(-num, -den)
    else
      Rational(num, den)
  }
}

@library
object Rational {

  implicit def bigIntToRat(n: scala.math.BigInt): Rational = Rational(n, 1)

  def apply(n: scala.math.BigInt): Rational = Rational(n, 1)

}
