import leon.lang._
import leon.collection._
import leon._

object RationalProps {

  def squarePos(r: Rational): Rational = {
    require(r.isRational)
    r * r
  } ensuring(_ >= Rational(0))

  def additionIsCommutative(p: Rational, q: Rational): Boolean = {
    require(p.isRational && q.isRational)
    p + q == q + p
  } holds

  def multiplicationIsCommutative(p: Rational, q: Rational): Boolean = {
    require(p.isRational && q.isRational)
    p * q == q * p
  } holds

  def lessThanIsTransitive(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p.isRational && q.isRational && r.isRational && p < q && q < r)
    p < r
  } holds

  def lessEqualsIsTransitive(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p.isRational && q.isRational && r.isRational && p <= q && q <= r)
    p <= r
  } holds

  def greaterThanIsTransitive(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p.isRational && q.isRational && r.isRational && p > q && q > r)
    p > r
  } holds

  def greaterEqualsIsTransitive(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p.isRational && q.isRational && r.isRational && p >= q && q >= r)
    p >= r
  } holds

  def distributionMult(p: Rational, q: Rational, r: Rational): Boolean = {
    require(p.isRational && q.isRational && r.isRational)
    (p*(q + r)) ~ (p*q + p*r)
  } holds

}
