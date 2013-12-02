package leon
package utils

import java.io.File

abstract class Position {
  val line: Int
  val col: Int
  val file: File

  def < (that: Position) = {
    (this.file == that.file) && (this.line < that.line || this.col < that.col)
  }

  override def toString = line+":"+col
  def isDefined = true
}

case class OffsetPosition(line: Int, col: Int, file: File) extends Position

case class RangePosition(lineFrom: Int, colFrom: Int, lineTo: Int, colTo: Int, file: File) extends Position {
  val line = lineFrom
  val col  = colFrom

  override def toString = lineFrom+":"+colFrom+"->"+lineTo+":"+colTo
}

case object NoPosition extends Position {
  val line = -1
  val col  = -1
  val file = null

  override def toString = "?:?"
  override def isDefined = false
}


trait Positioned {
  private[this] var _pos: Position = NoPosition

  def setPos(pos: Position): this.type = {
    _pos = pos
    this
  }

  def setPos(that: Positioned): this.type = {
    _pos = that.getPos
    this
  }

  def getPos = {
    _pos
  }
}
