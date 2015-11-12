package leon.lang

import leon.annotation._

/**
 * @author Mikael
 */
object StrOps {
  @ignore
  def concat(a: String, b: String): String = {
    a + b
  }
  @ignore
  def length(a: String): BigInt = {
    BigInt(a.length)
  }
  @ignore
  def substring(a: String, start: BigInt, end: BigInt): String = {
    if(start > end || start >= length(a) || end <= 0) "" else a.substring(start.toInt, end.toInt)
  }
  @ignore
  def bigIntToString(a: BigInt): String = {
    a.toString
  }
  @ignore
  def intToString(a: Int): String = {
    a.toString
  }
  @ignore
  def doubleToString(a: Double): String = {
    a.toString
  }
  def booleanToString(a: Boolean): String = {
    if(a) "true" else "false"
  }
  @ignore
  def charToString(a: Char): String = {
    a.toString
  }
  @ignore
  def realToString(a: Real): String = ???
}