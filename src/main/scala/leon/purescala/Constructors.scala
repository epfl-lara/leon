/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import utils._

object Constructors {
  import Trees._
  import Common._
  import TypeTrees._

  def tupleSelect(t: Expr, index: Int) = t match {
    case Tuple(es) =>
      es(index-1)
    case _ =>
      TupleSelect(t, index)
  }

  def letTuple(binders: Seq[Identifier], value: Expr, body: Expr) = binders match {
    case Nil =>
      body
    case x :: Nil =>
      Let(x, tupleSelect(value, 1), body)
    case xs =>
      LetTuple(xs, value, body)
  }

  def tupleChoose(ch: Choose): Expr = {
    if (ch.vars.size > 1) {
      ch
    } else {
      Tuple(Seq(ch))
    }
  }

  def tupleWrap(es: Seq[Expr]): Expr = if (es.size > 1) {
    Tuple(es)
  } else {
    es.head
  }

  private def filterCases(scrutinee: Expr, cases: Seq[MatchCase]): Seq[MatchCase] = {
    scrutinee.getType match {
      case c: CaseClassType =>
        cases.filter(_.pattern match {
          case CaseClassPattern(_, cct, _) if cct.classDef != c.classDef => false
          case _ => true
        })

      case _: TupleType | Int32Type | BooleanType | UnitType | _: AbstractClassType =>
        cases

      case t =>
        scala.sys.error("Constructing match expression on non-supported type: "+t)
    }
  }

  def gives(scrutinee : Expr, cases : Seq[MatchCase]) : Gives =
    Gives(scrutinee, filterCases(scrutinee, cases))
  
  def matchExpr(scrutinee : Expr, cases : Seq[MatchCase]) : MatchExpr = 
    MatchExpr(scrutinee, filterCases(scrutinee, cases))

  def and(exprs: Expr*): Expr = {
    val flat = exprs.flatMap(_ match {
      case And(es) => es
      case o => Seq(o)
    })

    var stop = false
    val simpler = for(e <- flat if !stop && e != BooleanLiteral(true)) yield {
      if(e == BooleanLiteral(false)) stop = true
      e
    }

    simpler match {
      case Seq()  => BooleanLiteral(true)
      case Seq(x) => x
      case _      => And(simpler)
    }
  }

  def andJoin(es: Seq[Expr]) = and(es :_*)

  def or(exprs: Expr*): Expr = {
    val flat = exprs.flatMap(_ match {
      case Or(es) => es
      case o => Seq(o)
    })

    var stop = false
    val simpler = for(e <- flat if !stop && e != BooleanLiteral(false)) yield {
      if(e == BooleanLiteral(true)) stop = true
      e
    }

    simpler match {
      case Seq()  => BooleanLiteral(false)
      case Seq(x) => x
      case _      => Or(simpler)
    }
  }

  def orJoin(es: Seq[Expr]) = or(es :_*)

  def not(e: Expr): Expr = e match {
    case Not(e)            => e
    case BooleanLiteral(v) => BooleanLiteral(!v)
    case _                 => Not(e)
  }

  def implies(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (BooleanLiteral(false), _) => BooleanLiteral(true)
    case (_, BooleanLiteral(true))  => BooleanLiteral(true)
    case (BooleanLiteral(true), r)  => r
    case (l, BooleanLiteral(false)) => Not(l)
    case (l1, Implies(l2, r2))      => implies(and(l1, l2), r2)
    case _                          => Implies(lhs, rhs)
  }
}
