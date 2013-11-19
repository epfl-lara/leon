package leon.sexpr

object Tokens {

  sealed trait Token

  case object OParen              extends Token /* ( */
  case object CParen              extends Token /* ) */

  case class StringLit(s: String) extends Token /* "hello" */
  case class SymbolLit(s: String) extends Token /* hello */
  case class IntLit(n: Int)       extends Token /* 42 */
  case class DoubleLit(d: Double) extends Token /* 42.24 */

}
