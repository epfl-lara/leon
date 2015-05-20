import leon.lang._
import leon.collection._
import leon._

object DivSemantics {

  def identity1(x: BigInt, y: BigInt): Boolean = {
    require(y > 0)
    - (x / y) == (-x)/y
  } ensuring(res => res)

  def identity2(x: BigInt): Boolean = {
    -(x / 2) == -x/2
  } ensuring(res => res)

  def identity3(x: BigInt): Boolean = {
    -(x / 2) == x / -2
  } ensuring(res => res)

  //def identity4(x: BigInt, y: BigInt): Boolean = {
  //  require(y > 0)
  //  - (x % y) == (-x)%y
  //} ensuring(res => res)

  def identity5(x: BigInt): Boolean = {
    x % 2 == x % -2
  } ensuring(res => res)

  def identity6(x: BigInt): Boolean = {
    require(x != 0)
    5 % x == 5 % -x
  } ensuring(res => res)

  def identity1Scoped(x: BigInt, y: BigInt): Boolean = {
    require(y > 0)
    val r1 = x / y
    val r2 = (-x) / y
    - r1 == r2
  } ensuring(res => res)


  def basic1(): Boolean = {
    -3 / 2 == -1
  } ensuring(res => res)
  def basic2(): Boolean = {
    -3 / -2 == 1
  } ensuring(res => res)
  def basic3(): Boolean = {
    3 / -2 == -1
  } ensuring(res => res)
  def basic4(): Boolean = {
    3 % -2 == 1
  } ensuring(res => res)
  def basic5(): Boolean = {
    -3 % -2 == -1
  } ensuring(res => res)
  def basic6(): Boolean = {
    -3 % 2 == -1
  } ensuring(res => res)

}
