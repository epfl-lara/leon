package leon
package horncl

object Tokens {

  sealed trait Token

  case object OParen extends Token /* ( */
  case object CParen extends Token /* ) */

  case class StringLit(s: String) extends Token /* "hello" */
  case class SymbolLit(s: String) extends Token /* hello */
  case class QualifiedSymbol(pre: Option[String], post: String) extends Token /* foo:bar */
  case class IntLit(n: BigInt) extends Token /* 42, #b101, #xFF1D */
  case class DoubleLit(d: Double) extends Token /* 42.24 */

}
