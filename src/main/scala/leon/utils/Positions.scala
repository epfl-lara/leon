/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import java.io.File

abstract class Position extends Ordered[Position] {
  val line: Int
  val col: Int
  val file: File

  def compare(that: Position) = {
    if (this.file == that.file) {
      val ld = this.line - that.line
      if (ld == 0) {
        this.col - that.col
      } else {
        ld
      }
    } else {
      if (this.file eq null) {
        -1
      } else if (that.file eq null) {
        +1
      } else {
        this.file.getPath.compare(that.file.getPath)
      }
    }
  }

  def fullString: String

  def isDefined: Boolean
}

object Position {
  def between(a: Position, b: Position): Position = {
    if (a.file == b.file) {
      if (a.line == b.line && a.col == b.col) {
        a
      } else {
        val (from, to) = if (a < b) (a, b) else (b, a)

        (from, to) match {
          case (p1: OffsetPosition, p2: OffsetPosition) =>
            RangePosition(p1.line, p1.col, p1.point, p2.line, p2.col, p2.point, p1.file)
          case (p1: RangePosition, p2: RangePosition) =>
            RangePosition(p1.lineFrom, p1.colFrom, p1.pointFrom, p2.lineTo, p2.colTo, p2.pointTo, p1.file)
          case (p1: OffsetPosition, p2: RangePosition) =>
            RangePosition(p1.line, p1.col, p1.point, p2.lineTo, p2.colTo, p2.pointTo, p1.file)
          case (p1: RangePosition, p2: OffsetPosition) =>
            RangePosition(p1.lineFrom, p1.colFrom, p1.pointFrom, p2.line, p2.col, p2.point, p1.file)
          case (a,b) =>
            a
        }
      }
    } else {
      a
    }
  }
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
