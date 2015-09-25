/* Copyright 2009-2015 EPFL, Lausanne */

import leon.monads.state._
import leon.collection._

object StackEvaluator {

  import State._

  abstract class Expr
  case class Plus(e1: Expr, e2: Expr) extends Expr
  case class Minus(e1: Expr, e2: Expr) extends Expr
  case class UMinus(e: Expr) extends Expr
  case class Lit(i: BigInt) extends Expr

  def push(i: BigInt) = State[List[BigInt], Unit]( s => ( (), i :: s) )
  def pop: State[List[BigInt], BigInt] = for {
    l <- get
    _ <- put(l.tailOption.getOrElse(Nil[BigInt]()))
  } yield l.headOption.getOrElse(0)


  def evalM(e: Expr): State[List[BigInt], Unit] = e match {
    case Plus(e1, e2) =>
      for {
        _ <- evalM(e1)
        _ <- evalM(e2)
        i2 <- pop
        i1 <- pop
        _ <- push(i1 + i2)
      } yield(())
    case Minus(e1, e2) =>
      for {
        _ <- evalM(e1)
        _ <- evalM(e2)
        i2 <- pop
        i1 <- pop
        _ <- push(i1 - i2)
      } yield(())
    case UMinus(e) =>
      evalM(e) >> pop >>= (i => push(-i))
    case Lit(i) =>
      push(i)
  }

  def eval(e: Expr): BigInt = e match {
    case Plus(e1, e2) =>
      eval(e1) + eval(e2)
    case Minus(e1, e2) =>
      eval(e1) - eval(e2)
    case UMinus(e) =>
      -eval(e)
    case Lit(i) =>
      i
  }

  def empty = List[BigInt]()

  //def evalVsEval(e: Expr) = {
  //  evalM(e).exec(empty).head == eval(e)
  //}.holds

}
