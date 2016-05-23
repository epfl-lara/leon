package leon.game2048

import leon.lang._
import leon.lang.Bag
import leon.annotation._
import leon.lang.StaticChecks._

import leon.util.Random

object Game2048 {

  case class Cell(var n: Option[BigInt]) {
    require(n.forall(v => v >= 0))

    def points: BigInt = n.getOrElse(0)

    def containsPoints: Boolean = n.nonEmpty
    def isEmpty: Boolean = n.isEmpty

    def canMerge(that: Cell): Boolean = that.n.nonEmpty && that.n == this.n

    def emptyAsInt: BigInt = if(n.isEmpty) 1 else 0

    def contentAsBag: Bag[BigInt] = n match {
      case None() => Bag.empty[BigInt]
      case Some(m) => Bag(m -> BigInt(1))
    }
    def content: Set[BigInt] = n match {
      case None() => Set.empty[BigInt]
      case Some(m) => Set(m)
    }
  }

  case class LevelMap(
    c11: Cell, c12: Cell, c13: Cell, c14: Cell,
    c21: Cell, c22: Cell, c23: Cell, c24: Cell,
    c31: Cell, c32: Cell, c33: Cell, c34: Cell,
    c41: Cell, c42: Cell, c43: Cell, c44: Cell
  ) {

    def content: Set[BigInt] = c11.content ++ c12.content ++ c13.content ++ c14.content ++
                               c21.content ++ c22.content ++ c23.content ++ c24.content ++
                               c31.content ++ c32.content ++ c33.content ++ c34.content ++
                               c41.content ++ c42.content ++ c43.content ++ c44.content

    def contentAsBag: Bag[BigInt] = c11.contentAsBag ++ c12.contentAsBag ++ c13.contentAsBag ++ c14.contentAsBag ++
                                    c21.contentAsBag ++ c22.contentAsBag ++ c23.contentAsBag ++ c24.contentAsBag ++
                                    c31.contentAsBag ++ c32.contentAsBag ++ c33.contentAsBag ++ c34.contentAsBag ++
                                    c41.contentAsBag ++ c42.contentAsBag ++ c43.contentAsBag ++ c44.contentAsBag 

    def totalPoints: BigInt =
      c11.points + c12.points + c13.points + c14.points +
      c21.points + c22.points + c23.points + c24.points +
      c31.points + c32.points + c33.points + c34.points +
      c41.points + c42.points + c43.points + c44.points

    def existsEmptyCell: Boolean = c11.isEmpty || c12.isEmpty || c13.isEmpty || c14.isEmpty ||
                                   c21.isEmpty || c22.isEmpty || c23.isEmpty || c24.isEmpty ||
                                   c31.isEmpty || c32.isEmpty || c33.isEmpty || c34.isEmpty ||
                                   c41.isEmpty || c42.isEmpty || c43.isEmpty || c44.isEmpty

    def nbEmptyCells: BigInt = c11.emptyAsInt + c12.emptyAsInt + c13.emptyAsInt + c14.emptyAsInt +
                               c21.emptyAsInt + c22.emptyAsInt + c23.emptyAsInt + c24.emptyAsInt +
                               c31.emptyAsInt + c32.emptyAsInt + c33.emptyAsInt + c34.emptyAsInt +
                               c41.emptyAsInt + c42.emptyAsInt + c43.emptyAsInt + c44.emptyAsInt


    //def canMove: Boolean = nbEmptyCells > 0 || 

    def nthFree(n: BigInt): BigInt = {
      require(n < nbEmptyCells)
      var toSkip = n
      var res: BigInt = -1

      if(c11.isEmpty && toSkip == 0 && res == -1) {
        res = 0
      } else if(c11.isEmpty) {
        toSkip -= 1
      }

      if(c12.isEmpty && toSkip == 0 && res == -1) {
        res = 1
      } else if(c12.isEmpty) {
        toSkip -= 1
      }

      if(c13.isEmpty && toSkip == 0 && res == -1) {
        res = 2
      } else if(c13.isEmpty) {
        toSkip -= 1
      }

      if(c14.isEmpty && toSkip == 0 && res == -1) {
        res = 3
      } else if(c14.isEmpty) {
        toSkip -= 1
      }

      if(c21.isEmpty && toSkip == 0 && res == -1) {
        res = 4
      } else if(c21.isEmpty) {
        toSkip -= 1
      }

      if(c22.isEmpty && toSkip == 0 && res == -1) {
        res = 5
      } else if(c22.isEmpty) {
        toSkip -= 1
      }

      if(c23.isEmpty && toSkip == 0 && res == -1) {
        res = 6
      } else if(c23.isEmpty) {
        toSkip -= 1
      }

      if(c24.isEmpty && toSkip == 0 && res == -1) {
        res = 7
      } else if(c24.isEmpty) {
        toSkip -= 1
      }

      if(c31.isEmpty && toSkip == 0 && res == -1) {
        res = 8
      } else if(c31.isEmpty) {
        toSkip -= 1
      }

      if(c32.isEmpty && toSkip == 0 && res == -1) {
        res = 9
      } else if(c32.isEmpty) {
        toSkip -= 1
      }

      if(c33.isEmpty && toSkip == 0 && res == -1) {
        res = 10
      } else if(c33.isEmpty) {
        toSkip -= 1
      }

      if(c34.isEmpty && toSkip == 0 && res == -1) {
        res = 11
      } else if(c34.isEmpty) {
        toSkip -= 1
      }

      if(c41.isEmpty && toSkip == 0 && res == -1) {
        res = 12
      } else if(c41.isEmpty) {
        toSkip -= 1
      }

      if(c42.isEmpty && toSkip == 0 && res == -1) {
        res = 13
      } else if(c42.isEmpty) {
        toSkip -= 1
      }

      if(c43.isEmpty && toSkip == 0 && res == -1) {
        res = 14
      } else if(c43.isEmpty) {
        toSkip -= 1
      }

      if(c44.isEmpty && toSkip == 0 && res == -1) {
        res = 15
      } else if(c44.isEmpty) {
        toSkip -= 1
      }

      res
    } ensuring(res => res >= n && res < 16)

    @ignore
    def cells: Vector[Cell] = Vector(c11, c12, c13, c14,
                                     c21, c22, c23, c24,
                                     c31, c32, c33, c34,
                                     c41, c42, c43, c44)
  }


  /* check that there are no holes in the middle of a row */
  def noHoles(c1: Cell, c2: Cell, c3: Cell, c4: Cell): Boolean = {
    if(c1.isEmpty) c2.isEmpty && c3.isEmpty && c4.isEmpty
    else if(c2.isEmpty) c3.isEmpty && c4.isEmpty
    else if(c3.isEmpty) c4.isEmpty
    else true
  }
  def noMergesOpportunities(c1: Cell, c2: Cell, c3: Cell, c4: Cell): Boolean = {
    !c1.canMerge(c2) && !c2.canMerge(c3) && !c3.canMerge(c4)
  }

  //slide everything to the left, filling empty spaces
  def slideLeft(c1: Cell, c2: Cell, c3: Cell, c4: Cell): Unit = {
    if(c3.isEmpty) {
      c3.n = c4.n
      c4.n = None()
    }
    if(c2.isEmpty) {
      c2.n = c3.n
      c3.n = c4.n
      c4.n = None()
    }
    if(c1.isEmpty) {
      c1.n = c2.n
      c2.n = c3.n
      c3.n = c4.n
      c4.n = None()
    }
  } ensuring(_ =>
    c1.points + c2.points + c3.points + c4.points == old(c1).points + old(c2).points + old(c3).points + old(c4).points &&
    noHoles(c1, c2, c3, c4)
  )


  //perform a left slide of the 4 cells. This can be used for any
  //4 celles in any direction, as long as the 4 cells are passed
  //in a coherent order to slideLeft. Merge any required cells
  //together
  def mergeLeft(c1: Cell, c2: Cell, c3: Cell, c4: Cell): Unit = {
    slideLeft(c1, c2, c3, c4)
    if(c3.canMerge(c4)) {
      merge(c4, c3)
    }
    if(c2.canMerge(c3)) {
      merge(c3, c2)
    }
    if(c1.canMerge(c2)) {
      merge(c2, c1)
    }
    slideLeft(c1, c2, c3, c4)
  } ensuring(_ =>
    c1.points + c2.points + c3.points + c4.points == old(c1).points + old(c2).points + old(c3).points + old(c4).points &&
    noHoles(c1, c2, c3, c4)
    //noMergesOpportunities(c1, c2, c3, c4)
  )

  /* check that a left move makes sense (either a hole to fill or a merge opportunity) */
  def canSlideLeft(c1: Cell, c2: Cell, c3: Cell, c4: Cell): Boolean = {
    !noHoles(c1, c2, c3, c4) || c1.canMerge(c2) || c2.canMerge(c3) || c3.canMerge(c4)
  }
  def canMoveLeft(map: LevelMap): Boolean = {
    canSlideLeft(map.c11, map.c12, map.c13, map.c14) ||
    canSlideLeft(map.c21, map.c22, map.c23, map.c24) ||
    canSlideLeft(map.c31, map.c32, map.c33, map.c34) ||
    canSlideLeft(map.c41, map.c42, map.c43, map.c44)
  }
  def canMoveUp(map: LevelMap): Boolean = {
    canSlideLeft(map.c11, map.c21, map.c31, map.c41) ||
    canSlideLeft(map.c12, map.c22, map.c32, map.c42) ||
    canSlideLeft(map.c13, map.c23, map.c33, map.c43) ||
    canSlideLeft(map.c14, map.c24, map.c34, map.c44)
  }
  def canMoveRight(map: LevelMap): Boolean = {
    canSlideLeft(map.c14, map.c13, map.c12, map.c11) ||
    canSlideLeft(map.c24, map.c23, map.c22, map.c21) ||
    canSlideLeft(map.c34, map.c33, map.c32, map.c31) ||
    canSlideLeft(map.c44, map.c43, map.c42, map.c41)
  }
  def canMoveDown(map: LevelMap): Boolean = {
    canSlideLeft(map.c41, map.c31, map.c21, map.c11) ||
    canSlideLeft(map.c42, map.c32, map.c22, map.c12) ||
    canSlideLeft(map.c43, map.c33, map.c23, map.c13) ||
    canSlideLeft(map.c44, map.c34, map.c24, map.c14)
  }

  //this only merges once, not recursively, thus disprove the final noMergesOpportunities postcondition
  //def mergeLeftNoRecursive(c1: Cell, c2: Cell, c3: Cell, c4: Cell): Unit = {
  //  slideLeft(c1, c2, c3, c4)
  //  if(c3.canMerge(c4)) {
  //    merge(c4, c3)
  //  }
  //  if(c2.canMerge(c3)) {
  //    merge(c3, c2)
  //  }
  //  if(c1.canMerge(c2)) {
  //    merge(c2, c1)
  //  }
  //  slideLeft(c1, c2, c3, c4)
  //} ensuring(_ =>
  //  c1.points + c2.points + c3.points + c4.points == old(c1).points + old(c2).points + old(c3).points + old(c4).points &&
  //  noHoles(c1, c2, c3, c4) &&
  //  noMergesOpportunities(c1, c2, c3, c4)
  //)

  def moveLeft(map: LevelMap): Unit = {
    require(canMoveLeft(map))
    mergeLeft(map.c11, map.c12, map.c13, map.c14)
    mergeLeft(map.c21, map.c22, map.c23, map.c24)
    mergeLeft(map.c31, map.c32, map.c33, map.c34)
    mergeLeft(map.c41, map.c42, map.c43, map.c44)
  } ensuring(_ => 
    map.totalPoints == old(map).totalPoints &&
    noHoles(map.c11, map.c12, map.c13, map.c14) &&
    noHoles(map.c21, map.c22, map.c23, map.c24) &&
    noHoles(map.c31, map.c32, map.c33, map.c34) &&
    noHoles(map.c41, map.c42, map.c43, map.c44)
  )

  def moveUp(map: LevelMap): Unit = {
    require(canMoveUp(map))
    mergeLeft(map.c11, map.c21, map.c31, map.c41)
    mergeLeft(map.c12, map.c22, map.c32, map.c42)
    mergeLeft(map.c13, map.c23, map.c33, map.c43)
    mergeLeft(map.c14, map.c24, map.c34, map.c44)
  } ensuring(_ => 
    map.totalPoints == old(map).totalPoints &&
    noHoles(map.c11, map.c21, map.c31, map.c41) &&
    noHoles(map.c12, map.c22, map.c32, map.c42) &&
    noHoles(map.c13, map.c23, map.c33, map.c43) &&
    noHoles(map.c14, map.c24, map.c34, map.c44)
  )


  def moveRight(map: LevelMap): Unit = {
    require(canMoveRight(map))
    mergeLeft(map.c14, map.c13, map.c12, map.c11)
    mergeLeft(map.c24, map.c23, map.c22, map.c21)
    mergeLeft(map.c34, map.c33, map.c32, map.c31)
    mergeLeft(map.c44, map.c43, map.c42, map.c41)
  } ensuring(_ =>
    map.totalPoints == old(map).totalPoints &&
    noHoles(map.c14, map.c13, map.c12, map.c11) &&
    noHoles(map.c24, map.c23, map.c22, map.c21) &&
    noHoles(map.c34, map.c33, map.c32, map.c31) &&
    noHoles(map.c44, map.c43, map.c42, map.c41)
  )

  def moveDown(map: LevelMap): Unit = {
    require(canMoveDown(map))
    mergeLeft(map.c41, map.c31, map.c21, map.c11)
    mergeLeft(map.c42, map.c32, map.c22, map.c12)
    mergeLeft(map.c43, map.c33, map.c23, map.c13)
    mergeLeft(map.c44, map.c34, map.c24, map.c14)
  } ensuring(_ => 
    map.totalPoints == old(map).totalPoints &&
    noHoles(map.c41, map.c31, map.c21, map.c11) &&
    noHoles(map.c42, map.c32, map.c22, map.c12) &&
    noHoles(map.c43, map.c33, map.c23, map.c13) &&
    noHoles(map.c44, map.c34, map.c24, map.c14)
  )


  /*
   * merge `that` into `into`, clearing `that` and setting `into` to
   * the right value.
   */
  def merge(that: Cell, into: Cell): Unit = {
    require(that.n.nonEmpty && that.n == into.n)
    val tmp = that.n.get
    that.n = None()
    into.n = Some(into.n.get + tmp)
  } ensuring(_ => into.points + that.points == old(into).points + old(that).points)



  def setRandomCell(map: LevelMap, v: BigInt)(implicit state: Random.State): Unit = {
    require(map.existsEmptyCell && (v == 2 || v == 4))

    val nbEmptyCells = map.nbEmptyCells
    val randomIndex = leon.util.Random.nextBigInt(nbEmptyCells)
    val realIndex = map.nthFree(randomIndex)

    if(realIndex == 0) {
      assert(map.c11.isEmpty)
      map.c11.n = Some(v)
    } else if(realIndex == 1) {
      map.c12.n = Some(v)
    } else if(realIndex == 2) {
      map.c13.n = Some(v)
    } else if(realIndex == 3) {
      map.c14.n = Some(v)
    } else if(realIndex == 4) {
      map.c21.n = Some(v)
    } else if(realIndex == 5) {
      map.c22.n = Some(v)
    } else if(realIndex == 6) {
      map.c23.n = Some(v)
    } else if(realIndex == 7) {
      map.c24.n = Some(v)
    } else if(realIndex == 8) {
      assert(map.c31.isEmpty)
      map.c31.n = Some(v)
    } else if(realIndex == 9) {
      assert(map.c32.isEmpty)
      map.c32.n = Some(v)
    } else if(realIndex == 10) {
      assert(map.c33.isEmpty)
      map.c33.n = Some(v)
    } else if(realIndex == 11) {
      assert(map.c34.isEmpty)
      map.c34.n = Some(v)
    } else if(realIndex == 12) {
      assert(map.c41.isEmpty)
      map.c41.n = Some(v)
    } else if(realIndex == 13) {
      assert(map.c42.isEmpty)
      map.c42.n = Some(v)
    } else if(realIndex == 14) {
      map.c43.n = Some(v)
    } else if(realIndex == 15) {
      map.c44.n = Some(v)
    }

  } ensuring(_ => {
    map.nbEmptyCells == old(map).nbEmptyCells - 1 &&
    map.totalPoints == old(map).totalPoints + v &&
    map.content == old(map).content + v
  })


  def popNumber(m: LevelMap)(implicit state: Random.State): Unit = {
    require(m.existsEmptyCell)
    val value: BigInt = 2*(1+leon.util.Random.nextBigInt(2))
    setRandomCell(m, value)
  }

}
