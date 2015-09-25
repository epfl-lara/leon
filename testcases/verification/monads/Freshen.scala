/* Copyright 2009-2015 EPFL, Lausanne */

import leon.monads.state._
import leon.lang._

object Freshen {

  import State._
  import leon.lang.string._

  case class Id(name: String, id: BigInt)

  abstract class Expr
  case class EVar(id: Id) extends Expr
  case class EAbs(v: Id, body: Expr) extends Expr
  case class EApp(f: Expr, arg: Expr) extends Expr

  case class EState(counters: Map[String, BigInt])

  def addVar(name: String): State[EState, Id] = for {
    s <- get[EState]
    newId = if (s.counters.contains(name)) s.counters(name) + 1 else BigInt(0)
    _ <- put( EState(s.counters + (name -> newId) ) )
  } yield Id(name, newId)

  def freshen(e: Expr): State[EState, Expr] = e match {
    case EVar(Id(name, id)) =>
      for {
        s <- get
      } yield {
        val newId = if (s.counters.contains(name)) s.counters(name) else id
        EVar(Id(name, newId))
      }
    case EAbs(v, body) =>
      for {
        v2    <- addVar(v.name)
        body2 <- freshen(body)
      } yield EAbs(v2, body2)
    case EApp(f, arg) =>
      for {
      // We need to freshen both f and arg with the initial state,
      // so we save it here
        init <- get
        f2   <- freshen(f)
        _    <- put(init)
        arg2 <- freshen(arg)
      } yield EApp(f2, arg2)
  }

  val empty = EState(Map[String, BigInt]())

  def freshenNames(e: Expr): Expr = empty >:: freshen(e)

}