/* Copyright 2009-2014 EPFL, Lausanne */

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

  def fullString: String

  def isDefined: Boolean
}

abstract class DefinedPosition extends Position {
  override def toString = line+":"+col
  override def fullString = file.getPath+":"+line+":"+col
  override def isDefined = true

  def focusBegin: OffsetPosition
  def focusEnd: OffsetPosition
}

case class OffsetPosition(line: Int, col: Int, point: Int, file: File) extends DefinedPosition {
  def focusBegin = this
  def focusEnd = this
}

case class RangePosition(lineFrom: Int, colFrom: Int, pointFrom: Int,
                         lineTo: Int, colTo: Int, pointTo: Int,
                         file: File) extends DefinedPosition {

  def focusEnd = OffsetPosition(lineTo, colTo, pointTo, file)
  def focusBegin = OffsetPosition(lineFrom, colFrom, pointFrom, file)

  val line = lineFrom
  val col  = colFrom
}

case object NoPosition extends Position {
  val line = -1
  val col  = -1
  val file = null

  override def toString = "?:?"
  override def fullString = "?:?:?"
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
