package leon.game2048

import scala.scalajs.js.JSApp
import scala.scalajs.js.annotation.JSExport

import org.scalajs.dom
import dom.document
import dom.html

import leon.lang._
import leon.util.Random
import leon.lang.StaticChecks._

@JSExport
object Main {

  import Game2048._
 
  type Ctx2D = dom.CanvasRenderingContext2D

  val CellWidth = 200
  val CellHeight = 200


  @JSExport
  def main(c: html.Canvas): Unit = {
    implicit val randomState = Random.newState
    println("Hello world!")

    val m = LevelMap(Cell(None()), Cell(None()), Cell(None()), Cell(None()),
                     Cell(None()), Cell(None()), Cell(None()), Cell(None()),
                     Cell(None()), Cell(None()), Cell(None()), Cell(None()),
                     Cell(None()), Cell(None()), Cell(None()), Cell(None()))

    m.c22.n = Some(2)
    m.c34.n = Some(4)
    renderGame(m)(c)

    document.onkeyup = (e: dom.KeyboardEvent) => {
      if(e.keyCode == 37) {
        println("left click")
        if(canMoveLeft(m)) {
          moveLeft(m)
          popNumber(m)
          renderGame(m)(c)
        }
      } else if(e.keyCode == 38) {
        println("up click")
        if(canMoveUp(m)) {
          moveUp(m)
          popNumber(m)
          renderGame(m)(c)
        }
      } else if(e.keyCode == 39) {
        println("right click")
        if(canMoveRight(m)) {
          moveRight(m)
          popNumber(m)
          renderGame(m)(c)
        }
      } else if(e.keyCode == 40) {
        println("down click")
        if(canMoveDown(m)) {
          moveDown(m)
          popNumber(m)
          renderGame(m)(c)
        }
      }
    }

  }

  def renderGame(map: LevelMap)(c: html.Canvas): Unit = {
    val ctx = c.getContext("2d").asInstanceOf[Ctx2D]

    ctx.clearRect(0, 0, 800, 800)

    var x = 0
    var y = 0

    renderCell(map.c11, x, y)(ctx)
    x += CellWidth
    renderCell(map.c12, x, y)(ctx)
    x += CellWidth
    renderCell(map.c13, x, y)(ctx)
    x += CellWidth
    renderCell(map.c14, x, y)(ctx)
    x = 0
    y += CellHeight

    renderCell(map.c21, x, y)(ctx)
    x += CellWidth
    renderCell(map.c22, x, y)(ctx)
    x += CellWidth
    renderCell(map.c23, x, y)(ctx)
    x += CellWidth
    renderCell(map.c24, x, y)(ctx)
    x = 0
    y += CellHeight

    renderCell(map.c31, x, y)(ctx)
    x += CellWidth
    renderCell(map.c32, x, y)(ctx)
    x += CellWidth
    renderCell(map.c33, x, y)(ctx)
    x += CellWidth
    renderCell(map.c34, x, y)(ctx)
    x = 0
    y += CellHeight

    renderCell(map.c41, x, y)(ctx)
    x += CellWidth
    renderCell(map.c42, x, y)(ctx)
    x += CellWidth
    renderCell(map.c43, x, y)(ctx)
    x += CellWidth
    renderCell(map.c44, x, y)(ctx)
    x = 0
    y += CellHeight

    ctx.stroke()

  }

  def renderCell(c: Game2048.Cell, x: Int, y: Int)(ctx: Ctx2D): Unit = {
    ctx.strokeStyle = "black"
    ctx.lineWidth = 6
    ctx.rect(x, y, CellWidth, CellHeight)

    ctx.font = "120px Georgia"
    val cx = (2*x + CellWidth)/2 - 30
    val cy = (2*y + CellHeight)/2 + 40
    ctx.fillText(c.n.map(_.toString).getOrElse(""), cx, cy)
  }


  /*
   * TODO: those should be part of the verified core
   *       One issue is that the code is using aliasing to return the random cell..
   */

  //def popNumber(m: LevelMap): Unit = {
  //  val cell = randomEmptyCell(m)
  //  println("poping number on cell: " + cell)
  //  cell.n = Some(2*(1+scala.util.Random.nextInt(2)))
  //}

  //def randomEmptyCell(m: LevelMap): Cell = {
  //  val emptyCells: Vector[Cell] = m.cells.filter(_.isEmpty)
  //  println("empty cells: " + emptyCells)
  //  val countEmpty = emptyCells.size
  //  val randomIndex = scala.util.Random.nextInt(countEmpty)
  //  println("random index: " + randomIndex)
  //  emptyCells(randomIndex)
  //}

}
