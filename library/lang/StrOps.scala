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
}