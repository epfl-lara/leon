package leon.gametictactoe

import leon.lang._
import leon.lang.Bag
import leon.annotation._
import leon.lang.StaticChecks._

import leon.util.Random

object GameTicTacToe {

  abstract class Player {
    def isCross: Boolean = this == PlayerCross
    def isCircle: Boolean = this == PlayerCircle

    def opponent: Player = this match {
      case PlayerCross => PlayerCircle
      case PlayerCircle => PlayerCross
    }
  }
  case object PlayerCross extends Player
  case object PlayerCircle extends Player

  case class Cell(var n: Option[Player]) {

    def crossAsInt: BigInt = n match {
      case Some(PlayerCross) => 1
      case _ => 0
    }

    def emptyAsInt: BigInt = if(n.isEmpty) 1 else 0

    def containsEntry: Boolean = n.nonEmpty
    def isEmpty: Boolean = n.isEmpty

    def matches(that: Cell): Boolean = this.containsEntry && this.n == that.n

  }

  case class LevelMap(
    c11: Cell, c12: Cell, c13: Cell,
    c21: Cell, c22: Cell, c23: Cell, 
    c31: Cell, c32: Cell, c33: Cell
  ) {
    require(totalEntries == totalXEntries + totalOEntries && invariantXAtMostOneMore)

    def invariantXAtMostOneMore: Boolean =
      (totalXEntries == totalOEntries+1 || totalXEntries == totalOEntries)

    def totalEntries: BigInt = 9 - nbEmptyCells

    def totalXEntries: BigInt =
      c11.crossAsInt + c12.crossAsInt + c13.crossAsInt +
      c21.crossAsInt + c22.crossAsInt + c23.crossAsInt +
      c31.crossAsInt + c32.crossAsInt + c33.crossAsInt

    def totalOEntries: BigInt = totalEntries - totalXEntries

    def existsEmptyCell: Boolean = c11.isEmpty || c12.isEmpty || c13.isEmpty ||
                                   c21.isEmpty || c22.isEmpty || c23.isEmpty ||
                                   c31.isEmpty || c32.isEmpty || c33.isEmpty

    def nbEmptyCells: BigInt = c11.emptyAsInt + c12.emptyAsInt + c13.emptyAsInt +
                               c21.emptyAsInt + c22.emptyAsInt + c23.emptyAsInt +
                               c31.emptyAsInt + c32.emptyAsInt + c33.emptyAsInt

    def fill(j: BigInt, i: BigInt, player: Player): Unit = {
      require(canPlay(player) && canFill(j, i, player))
      if     (j == 1 && i == 1) c11.n = Some(player)
      else if(j == 1 && i == 2) c12.n = Some(player)
      else if(j == 1 && i == 3) c13.n = Some(player)
      else if(j == 2 && i == 1) c21.n = Some(player)
      else if(j == 2 && i == 2) c22.n = Some(player)
      else if(j == 2 && i == 3) c23.n = Some(player)
      else if(j == 3 && i == 1) c31.n = Some(player)
      else if(j == 3 && i == 2) c32.n = Some(player)
      else if(j == 3 && i == 3) c33.n = Some(player)
      else                      ()
    }

    def canFill(j: BigInt, i: BigInt, player: Player): Boolean = canPlay(player) && isFree(j, i)

    def isFree(j: BigInt, i: BigInt): Boolean =
      if     (j == 1 && i == 1) c11.isEmpty
      else if(j == 1 && i == 2) c12.isEmpty
      else if(j == 1 && i == 3) c13.isEmpty
      else if(j == 2 && i == 1) c21.isEmpty
      else if(j == 2 && i == 2) c22.isEmpty
      else if(j == 2 && i == 3) c23.isEmpty
      else if(j == 3 && i == 1) c31.isEmpty
      else if(j == 3 && i == 2) c32.isEmpty
      else if(j == 3 && i == 3) c33.isEmpty
      else                      false  

    def canPlay(player: Player): Boolean = player match {
      case PlayerCross => totalXEntries == totalOEntries
      case PlayerCircle => totalXEntries == totalOEntries + 1
    }

  }

  case class Game(map: LevelMap, var currentPlayer: Player) {
    //require(map.canPlay(currentPlayer))


    def doPlay(j: BigInt, i: BigInt): Unit = {
      require(map.canFill(j, i, currentPlayer) )
      map.fill(j, i, currentPlayer)
      currentPlayer = currentPlayer.opponent
    } ensuring(_ => map.canPlay(currentPlayer))

  }

  def checkGameEnded(map: LevelMap): Boolean = {
    val r1 = map.c11.matches(map.c12) && map.c12.matches(map.c13)
    val r2 = map.c21.matches(map.c22) && map.c22.matches(map.c23)
    val r3 = map.c31.matches(map.c32) && map.c32.matches(map.c33)
    val c1 = map.c11.matches(map.c21) && map.c21.matches(map.c31)
    val c2 = map.c12.matches(map.c22) && map.c22.matches(map.c32)
    val c3 = map.c13.matches(map.c23) && map.c23.matches(map.c33)
    val d1 = map.c11.matches(map.c22) && map.c22.matches(map.c33)
    val d2 = map.c31.matches(map.c22) && map.c22.matches(map.c13)
    r1 || r2 || r3 || c1 || c2 || c3 || d1 || d2 
  }

}
