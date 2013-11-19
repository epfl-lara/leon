package leon.sexpr

import Tokens._
import SExprs._

class Parser(lexer: Lexer) {

  private var _currentToken: Token = null
  private var _futureToken: Token = lexer.next
  private def next: Token = {
    _currentToken = _futureToken 
    _futureToken = lexer.next
    _currentToken
  }
  private def peek: Token = _futureToken

  def parse: SExpr = {
    next match {
      case OParen => {
        val buffer = new scala.collection.mutable.ListBuffer[SExpr]
        while(peek != CParen) {
          val child: SExpr = parse
          buffer.append(child)
        }
        SList(buffer.toList)
      }
      case IntLit(d) => SInt(d)
      case StringLit(s) => SString(s)
      case SymbolLit(s) => SSymbol(s)
      case DoubleLit(d) => SDouble(d)
      case CParen => sys.error("Unexpected token: " + CParen)
    }
  }

}
