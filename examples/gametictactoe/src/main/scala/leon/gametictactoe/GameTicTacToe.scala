package leon.gametictactoe

import leon.lang._
import leon.lang.Bag
import leon.annotation._
import leon.lang.StaticChecks._

import leon.util.Random

object GameTicTacToe {

  case class Cell(var n: Option[BigInt]) {
    require(n.forall(v => v >= 0))

    def entryInCell: BigInt = n.getOrElse(0)

    def containsEntry: Boolean = n.nonEmpty
    def isEmpty: Boolean = n.isEmpty

    def emptyAsInt: BigInt = if(n.isEmpty) 1 else 0
  }

  case class LevelMap(
    var c11: Cell, var c12: Cell, var c13: Cell,
    var c21: Cell, var c22: Cell, var c23: Cell, 
    var c31: Cell, var c32: Cell, var c33: Cell
  ) {

    def totalEntries: BigInt = 9 - nbEmptyCells

    def totalXEntries: BigInt =
      c11.entryInCell + c12.entryInCell + c13.entryInCell +
      c21.entryInCell + c22.entryInCell + c23.entryInCell +
      c31.entryInCell + c32.entryInCell + c33.entryInCell

    def totalOEntries: BigInt = totalEntries - totalXEntries

    def existsEmptyCell: Boolean = c11.isEmpty || c12.isEmpty || c13.isEmpty ||
                                   c21.isEmpty || c22.isEmpty || c23.isEmpty ||
                                   c31.isEmpty || c32.isEmpty || c33.isEmpty

    def nbEmptyCells: BigInt = c11.emptyAsInt + c12.emptyAsInt + c13.emptyAsInt +
                               c21.emptyAsInt + c22.emptyAsInt + c23.emptyAsInt +
                               c31.emptyAsInt + c32.emptyAsInt + c33.emptyAsInt

    def fill(j: BigInt, i: BigInt, x: BigInt): Unit = {
      if(j == 1 && i == 1) c11 = Cell(Some(x))
      else if(j == 1 && i == 2) c12 = Cell(Some(x))
      else if(j == 1 && i == 3) c13 = Cell(Some(x))
      else if(j == 2 && i == 1) c21 = Cell(Some(x))
      else if(j == 2 && i == 2) c22 = Cell(Some(x))
      else if(j == 2 && i == 3) c23 = Cell(Some(x))
      else if(j == 3 && i == 1) c31 = Cell(Some(x))
      else if(j == 3 && i == 2) c32 = Cell(Some(x))
      else if(j == 3 && i == 3) c33 = Cell(Some(x))
      else false
    }

    def canFill(j: BigInt, i: BigInt): Boolean = {
      if(j == 1 && i == 1) c11.isEmpty
      else if(j == 1 && i == 2) c12.isEmpty
      else if(j == 1 && i == 3) c13.isEmpty
      else if(j == 2 && i == 1) c21.isEmpty
      else if(j == 2 && i == 2) c22.isEmpty
      else if(j == 2 && i == 3) c23.isEmpty
      else if(j == 3 && i == 1) c31.isEmpty
      else if(j == 3 && i == 2) c32.isEmpty
      else if(j == 3 && i == 3) c33.isEmpty
      else false  
    }

    @ignore
    def cells: Vector[Cell] = Vector(c11, c12, c13,
                                     c21, c22, c23, 
                                     c31, c32, c33)
  }

  def checkGameEnded(map: LevelMap): Boolean = {
    val r1 = map.c11.containsEntry && map.c12.containsEntry && map.c13.containsEntry && (map.c11.entryInCell == map.c12.entryInCell) && (map.c12.entryInCell == map.c13.entryInCell)
    val r2 = map.c21.containsEntry && map.c22.containsEntry && map.c23.containsEntry && (map.c21.entryInCell == map.c22.entryInCell) && (map.c22.entryInCell == map.c23.entryInCell)
    val r3 = map.c31.containsEntry && map.c32.containsEntry && map.c33.containsEntry && (map.c31.entryInCell == map.c32.entryInCell) && (map.c32.entryInCell == map.c33.entryInCell)
    val c1 = map.c11.containsEntry && map.c21.containsEntry && map.c31.containsEntry && (map.c11.entryInCell == map.c21.entryInCell) && (map.c21.entryInCell == map.c31.entryInCell)
    val c2 = map.c12.containsEntry && map.c22.containsEntry && map.c32.containsEntry && (map.c12.entryInCell == map.c22.entryInCell) && (map.c22.entryInCell == map.c32.entryInCell)
    val c3 = map.c13.containsEntry && map.c23.containsEntry && map.c33.containsEntry && (map.c13.entryInCell == map.c23.entryInCell) && (map.c23.entryInCell == map.c33.entryInCell)
    val d1 = map.c11.containsEntry && map.c22.containsEntry && map.c33.containsEntry && (map.c11.entryInCell == map.c22.entryInCell) && (map.c22.entryInCell == map.c33.entryInCell)
    val d2 = map.c31.containsEntry && map.c22.containsEntry && map.c13.containsEntry && (map.c31.entryInCell == map.c22.entryInCell) && (map.c22.entryInCell == map.c13.entryInCell)
    r1 || r2 || r3 || c1 || c2 || c3 || d1 || d2 
  }

}
