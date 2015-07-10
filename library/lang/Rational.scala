/* Copyright 2009-2015 EPFL, Lausanne */

package leon.lang

import leon.annotation._

@library
case class Rational(numerator: BigInt, denominator: BigInt) {

  def +(that: Rational): Rational = {
    require(this.isRational && that.isRational)
    Rational(this.numerator*that.denominator + that.numerator*this.denominator, this.denominator*that.denominator)
  }

  def -(that: Rational): Rational = {
    require(this.isRational && that.isRational)
    Rational(this.numerator*that.denominator - that.numerator*this.denominator, this.denominator*that.denominator)
  }

  def *(that: Rational): Rational = {
    require(this.isRational && that.isRational)
    Rational(this.numerator*that.numerator, this.denominator*that.denominator)
  }

  def /(that: Rational): Rational = {
    require(this.isRational && that.isRational)
    Rational(this.numerator*that.denominator, this.denominator*that.numerator)
  }


  def ~(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    this.numerator*that.denominator == that.numerator*this.denominator
  }

  def <(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    if(this.denominator >= 0 && that.denominator >= 0)
      this.numerator*that.denominator < that.numerator*this.denominator
    else if(this.denominator >= 0 && that.denominator < 0)
      this.numerator*that.denominator > that.numerator*this.denominator
    else if(this.denominator < 0 && that.denominator >= 0)
      this.numerator*that.denominator > that.numerator*this.denominator
    else
      this.numerator*that.denominator < that.numerator*this.denominator
  }

  def <=(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    if(this.denominator >= 0 && that.denominator >= 0)
      this.numerator*that.denominator <= that.numerator*this.denominator
    else if(this.denominator >= 0 && that.denominator < 0)
      this.numerator*that.denominator >= that.numerator*this.denominator
    else if(this.denominator < 0 && that.denominator >= 0)
      this.numerator*that.denominator >= that.numerator*this.denominator
    else
      this.numerator*that.denominator <= that.numerator*this.denominator
  }

  def >(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    if(this.denominator >= 0 && that.denominator >= 0)
      this.numerator*that.denominator > that.numerator*this.denominator
    else if(this.denominator >= 0 && that.denominator < 0)
      this.numerator*that.denominator < that.numerator*this.denominator
    else if(this.denominator < 0 && that.denominator >= 0)
      this.numerator*that.denominator < that.numerator*this.denominator
    else
      this.numerator*that.denominator > that.numerator*this.denominator
  }

  def >=(that: Rational): Boolean = {
    require(this.isRational && that.isRational)
    if(this.denominator >= 0 && that.denominator >= 0)
      this.numerator*that.denominator >= that.numerator*this.denominator
    else if(this.denominator >= 0 && that.denominator < 0)
      this.numerator*that.denominator <= that.numerator*this.denominator
    else if(this.denominator < 0 && that.denominator >= 0)
      this.numerator*that.denominator <= that.numerator*this.denominator
    else
      this.numerator*that.denominator >= that.numerator*this.denominator
  }

  def nonZero: Boolean = {
    require(this.isRational)
    numerator != 0
  }

  def isRational: Boolean = denominator != 0
}

object Rational {

  implicit def bigIntToRat(n: BigInt): Rational = Rational(n, 1)

  def apply(n: BigInt): Rational = Rational(n, 1)
}
