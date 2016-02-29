import leon.lang._
import leon.collection._
import leon._

import scala.language.postfixOps

object RationalProps {

  def squarePos(r: Rational): Rational = {
    r * r
  } ensuring(_ >= Rational(0))

  def additionIsCommutative(p: Rational, q: Rational): Boolean = {
    p + q == q + p
  } holds

  def multiplicationIsCommutative(p: Rational, q: Rational): Boolean = {
    p * q == q * p
  } holds

  def lessThanIsTransitive(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p < q && q < r)
    p < r
  } holds

  def lessEqualsIsTransitive(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p <= q && q <= r)
    p <= r
  } holds

  def greaterThanIsTransitive(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p > q && q > r)
    p > r
  } holds

  def greaterEqualsIsTransitive(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p >= q && q >= r)
    p >= r
  } holds

  def distributionMult(p: Rational, q: Rational, r: Rational): Boolean = {
    (p*(q + r)) ~ (p*q + p*r)
  } holds

  def reciprocalIsCorrect(p: Rational): Boolean = {
    require(p.nonZero)
    (p * p.reciprocal) ~ Rational(1)
  } holds

  def additiveInverseIsCorrect(p: Rational): Boolean = {
    (p + (-p)) ~ Rational(0)
  } holds

  //should not hold because q could be 0
  def divByZero(p: Rational, q: Rational): Boolean = {
    ((p / q) * q) ~ p
  } holds

  def divByNonZero(p: Rational, q: Rational): Boolean = {
    require(q.nonZero)
    ((p / q) * q) ~ p
  } holds
  

  /*
   * properties of equivalence
   */

  def equivalentIsReflexive(p: Rational): Boolean = {
    p ~ p
  } holds

  def equivalentIsSymmetric(p: Rational, q: Rational): Boolean = {
    require(p ~ q)
    q ~ p
  } holds

  def equivalentIsTransitive(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p ~ q && q ~ r)
    p ~ r
  } holds
}
