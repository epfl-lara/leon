/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._
import leon.monads.state._
import leon.collection._

object TicTacToe {

  import State._

  abstract class Square
  case object UL extends Square
  case object U  extends Square
  case object UR extends Square
  case object L  extends Square
  case object C  extends Square
  case object R  extends Square
  case object DL extends Square
  case object D  extends Square
  case object DR extends Square

  @inline
  val winningSets: List[Set[Square]] = List(
    Set(UL, U, UR),
    Set( L, C,  R),
    Set(DL, D, DR),
    Set(UL, L, DL),
    Set( U, C,  D),
    Set(UR, R, DR),
    Set(UR, C, DL),
    Set(UL, C, DR)
  )

  @inline
  def wins(sqs: Set[Square]) = winningSets exists { _ subsetOf sqs}

  case class Board(xs: Set[Square], os: Set[Square])
  case class TState(b: Board, xHasMove: Boolean) // true = X, false = O

  @inline
  val init = TState(Board(Set.empty[Square], Set.empty[Square]), true)

  @inline
  def legalMove(b: Board, sq: Square) = !(b.xs ++ b.os).contains(sq)

  @inline
  def move(sq: Square): State[TState, Unit] = {
    modify[TState] { case TState(board, xHasMove) =>
      TState(
        if (xHasMove)
          Board(board.xs ++ Set(sq), board.os)
        else
          Board(board.xs, board.os ++ Set(sq)),
        if (legalMove(board, sq))
          !xHasMove
        else
          xHasMove
      )
    }
  }

  @inline
  def play(moves: List[Square]): Option[Boolean] = {
    val b = foldLeftM_ (move, moves).exec(init).b
    if (wins(b.xs)) Some(true)
    else if (wins(b.os)) Some(false)
    else None[Boolean]()
  }

  //def ex = {
  //  play(List(UL, UR, C, D, DR)) == Some(true)
  //}.holds

  //def gameEnds(moves: List[Square], oneMore: Square) = {
  //  val res1 = play(moves)
  //  val res2 = play(moves :+ oneMore)
  //  res1.isDefined ==> (res1 == res2)
  //}.holds
}