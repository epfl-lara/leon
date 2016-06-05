package leon.gametictactoe

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

  import GameTicTacToe._
 
  type Ctx2D = dom.CanvasRenderingContext2D

  val CellWidth = 300
  val CellHeight = 300


  @JSExport
  def main(c: html.Canvas): Unit = {
    implicit val randomState = Random.newState
    println("Welcome to Tic Tac Toe!")

    var m = LevelMap(Cell(None()), Cell(None()), Cell(None()),
                     Cell(None()), Cell(None()), Cell(None()), 
                     Cell(None()), Cell(None()), Cell(None()))

    renderGame(m)(c)

    var playerx = true

    // Mouse click for tictactoe

    c.onmousedown = {
      (e: dom.MouseEvent) => 
      (1 to 3).foreach { i =>
        (1 to 3).foreach { j =>
          if((e.clientX <= i * CellWidth) && (e.clientX >= (i - 1) * CellWidth) && (e.clientY <= j * CellHeight) && (e.clientY >= (j - 1) * CellWidth)) {
            println(s"at $i, $j")
            if(playerx && m.canFill(j, i)) {
              m.fill(j, i, 1)
              checkGameEnded(m)
              renderGame(m)(c)
              playerx = false
            }
            else if(!playerx && m.canFill(j, i)) {
              m.fill(j, i, 0)
              checkGameEnded(m)
              renderGame(m)(c)
              playerx = true
            }
          }
        }
      }

    }
  }

  def renderGame(map: LevelMap)(c: html.Canvas): Unit = {
    val ctx = c.getContext("2d").asInstanceOf[Ctx2D]

    ctx.clearRect(0, 0, 900, 900)

    var x = 0
    var y = 0

    renderCell(map.c11, x, y)(ctx)
    x += CellWidth
    renderCell(map.c12, x, y)(ctx)
    x += CellWidth
    renderCell(map.c13, x, y)(ctx)
    x = 0
    y += CellHeight

    renderCell(map.c21, x, y)(ctx)
    x += CellWidth
    renderCell(map.c22, x, y)(ctx)
    x += CellWidth
    renderCell(map.c23, x, y)(ctx)
    x = 0
    y += CellHeight

    renderCell(map.c31, x, y)(ctx)
    x += CellWidth
    renderCell(map.c32, x, y)(ctx)
    x += CellWidth
    renderCell(map.c33, x, y)(ctx)
    x = 0
    y += CellHeight

    ctx.stroke()
  }

  def renderCell(c: GameTicTacToe.Cell, x: Int, y: Int)(ctx: Ctx2D): Unit = {
    ctx.strokeStyle = "black"
    ctx.lineWidth = 6
    ctx.rect(x, y, CellWidth, CellHeight)

    ctx.font = "120px Georgia"
    val cx = (2*x + CellWidth)/2 - 30
    val cy = (2*y + CellHeight)/2 + 40
    val elem = c.n.map(_.toString).getOrElse("")
    if(elem == "1") ctx.fillText("X", cx, cy)
    else if(elem == "0") ctx.fillText("O", cx, cy)
    else ctx.fillText("", cx, cy)  
  }

}
