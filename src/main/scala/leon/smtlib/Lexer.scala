package leon
package smtlib

import Tokens._


class Lexer(reader: java.io.Reader) {

  private def isNewLine(c: Char) = c == '\n' || c == '\r'
  private def isBlank(c: Char) = c == '\n' || c == '\r' || c == ' '
  private def isSeparator(c: Char) = isBlank(c) || c == ')' || c == '('

  private var _currentChar: Char = (-1).toChar
  private var _futureChar: Char = reader.read.toChar

  private def nextChar: Char = {
    if(_futureChar == -1) 
      throw new java.io.EOFException
    _currentChar = _futureChar
    _futureChar = reader.read.toChar
    _currentChar
  }
  private def peek: Char = _futureChar

  def next: Token = {

    var c = nextChar
    while(isBlank(c))
      c = nextChar

    c match {
      case ';' => {
        while(!isNewLine(nextChar))
          ()
        next
      }
      case '(' => OParen
      case ')' => CParen
      case '"' => {
        val buffer = new scala.collection.mutable.ArrayBuffer[Char]
        var c = nextChar 
        while(c != '"') {
          buffer.append(c)
          c = nextChar
        }
        StringLit(new String(buffer.toArray))
      }
      case d if d.isDigit => {
        var intPart: Int = d.asDigit
        while(peek.isDigit) {
          intPart *= 10
          intPart += nextChar.asDigit
        }
        if(peek != '.')
          IntLit(intPart)
        else {
          nextChar
          var fracPart: Double = 0
          var base = 10
          while(peek.isDigit) {
            fracPart += nextChar.asDigit
            fracPart *= 10
            base *= 10
          }
          DoubleLit(intPart + fracPart/base)
        }
      }
      case s => {
        val buffer = new scala.collection.mutable.ArrayBuffer[Char]
        buffer.append(s)
        while(!isSeparator(peek)) {
          buffer.append(nextChar)
        }
        SymbolLit(new String(buffer.toArray))
      }
    }
  }

  def hasNext: Boolean = true

    

}
