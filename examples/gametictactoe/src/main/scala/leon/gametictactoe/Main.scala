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

    renderGame(m, "Start game with X")(c)

    var player: Player = PlayerCross

    // Mouse click for tictactoe

    c.onmousedown = {
      (e: dom.MouseEvent) => 
      (1 to 3).foreach { i =>
        (1 to 3).foreach { j =>
          if((e.clientX <= i * CellWidth) && (e.clientX > (i - 1) * CellWidth) && (e.clientY <= j * CellHeight) && (e.clientY > (j - 1) * CellHeight)) {
            println(s"at $i, $j")
            if(player.isCross && m.canFill(j, i, player)) {
              println("placing cross")
              m.fill(j, i, player)
              if(checkGameEnded(m)) {
                renderGameOver("X")(c)
              } else {
                renderGame(m, "O's turn")(c)  
              }
              player = PlayerCircle
            }
            else if(player.isCircle && m.canFill(j, i, player)) {
              println("placing circle")
              m.fill(j, i, player)
              if(checkGameEnded(m)) {
                renderGameOver("O")(c)
              } else {
                renderGame(m, "X's turn")(c)  
              }
              player = PlayerCross
            }
          }
        }
      }

    }
  }

  def renderGame(map: LevelMap, msg: String)(c: html.Canvas): Unit = {
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

    ctx.font = "20px Georgia"
    y -= 7
    x += 3
    ctx.fillText(msg, x, y)
    ctx.stroke()
  }

  def renderGameOver(player: String)(c: html.Canvas): Unit = {
    val ctx = c.getContext("2d").asInstanceOf[Ctx2D]

    ctx.clearRect(0, 0, 900, 900)

    var x = 0
    var y = CellHeight

    ctx.strokeStyle = "black"
    ctx.font = "40px Georgia"

    ctx.fillText(s"GAME OVER, $player wins!\nRefresh to restart!", x, y)
    ctx.stroke()
  }

  def renderCell(c: GameTicTacToe.Cell, x: Int, y: Int)(ctx: Ctx2D): Unit = {
    ctx.strokeStyle = "black"
    ctx.lineWidth = 6
    ctx.rect(x, y, CellWidth, CellHeight)

    ctx.font = "120px Georgia"
    val cx = (2*x + CellWidth)/2 - 30
    val cy = (2*y + CellHeight)/2 + 40
    val elem = c.n match {
      case Some(PlayerCross) => "X"
      case Some(PlayerCircle) => "O"
      case None() => ""
    }
    ctx.fillText(elem, cx, cy)
  }

}
