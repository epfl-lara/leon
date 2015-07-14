import leon.lang._
import leon.collection._
import leon._

import scala.language.postfixOps

object RealProps {

  def plusIsCommutative(a: Real, b: Real): Boolean = {
    a + b == b + a
  } holds

  def plusIsAssociative(a: Real, b: Real, c: Real): Boolean = {
    (a + b) + c == a + (b + c)
  } holds

  def timesIsCommutative(a: Real, b: Real): Boolean = {
    a * b == b * a
  } holds

  def timesIsAssociative(a: Real, b: Real, c: Real): Boolean = {
    (a * b) * c == a * (b * c)
  } holds

  def distributivity(a: Real, b: Real, c: Real): Boolean = {
    a*(b + c) == a*b + a*c
  } holds

  def lessEqualsTransitive(a: Real, b: Real, c: Real): Boolean = {
    require(a <= b && b <= c)
    a <= c
  } holds

  def lessThanTransitive(a: Real, b: Real, c: Real): Boolean = {
    require(a < b && b < c)
    a < c
  } holds

  def greaterEqualsTransitive(a: Real, b: Real, c: Real): Boolean = {
    require(a >= b && b >= c)
    a >= c
  } holds

  def greaterThanTransitive(a: Real, b: Real, c: Real): Boolean = {
    require(a > b && b > c)
    a > c
  } holds

  /* between any two real, there is another real */
  def density(a: Real, b: Real): Boolean = {
    require(a < b)
    val mid = (a + b) / Real(2)
    a < mid && mid < b
  } holds

  def identity1(a: Real): Boolean = {
    require(a != Real(0))
    a/a == Real(1)
  } holds

  def test(r: Real): Real = {
    r
  } ensuring(res => res >= Real(0))

  def findRoot(r: Real): Real = {
    r * r
  } ensuring(res => res != Real(4))

  //def findSqrt2(r: Real): Real = {
  //  r * r
  //} ensuring(res => res != Real(2))
}
