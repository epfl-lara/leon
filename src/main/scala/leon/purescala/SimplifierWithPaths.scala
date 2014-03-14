/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import Trees._
import TypeTrees._
import TreeOps._
import Extractors._
import solvers._

class SimplifierWithPaths(sf: SolverFactory[Solver]) extends TransformerWithPC {
  type C = List[Expr]

  val initC = Nil

  val solver = SimpleSolverAPI(sf)

  protected def register(e: Expr, c: C) = e :: c

  def impliedBy(e : Expr, path : Seq[Expr]) : Boolean = try {
    solver.solveVALID(Implies(And(path), e)) match {
      case Some(true) => true
      case _ => false
    }
  } catch {
    case _ : Exception => false
  }

  def contradictedBy(e : Expr, path : Seq[Expr]) : Boolean = try {
    solver.solveVALID(Implies(And(path), Not(e))) match {
      case Some(true) => true
      case _ => false
    }
  } catch {
    case _ : Exception => false
  }

  protected override def rec(e: Expr, path: C) = e match {
    case IfExpr(cond, thenn, elze) =>
      super.rec(e, path) match {
        case IfExpr(BooleanLiteral(true) , t, _) => t
        case IfExpr(BooleanLiteral(false), _, e) => e
        case ite => ite
      }

    case And(es) =>
      var soFar = path
      var continue = true
      var r = And(for(e <- es if continue) yield {
        val se = rec(e, soFar)
        if(se == BooleanLiteral(false)) continue = false
        soFar = register(se, soFar)
        se
      }).copiedFrom(e)

      if (continue) {
        r
      } else {
        BooleanLiteral(false).copiedFrom(e)
      }

    case MatchExpr(scrut, cases) =>
      val rs = rec(scrut, path)

      var stillPossible = true

      if (cases.exists(_.hasGuard)) {
        // unsupported for now
        e
      } else {
        MatchExpr(rs, cases.flatMap { c =>
          val patternExpr = conditionForPattern(rs, c.pattern, includeBinders = true)

          if (stillPossible && !contradictedBy(patternExpr, path)) {

            if (impliedBy(patternExpr, path)) {
              stillPossible = false
            }

            c match {
              case SimpleCase(p, rhs) =>
                Some(SimpleCase(p, rec(rhs, patternExpr +: path)).copiedFrom(c))
              case GuardedCase(_, _, _) =>
                sys.error("woot.")
            }
          } else {
            None
          }
        }).copiedFrom(e)
      }

    case Or(es) =>
      var soFar = path
      var continue = true
      var r = Or(for(e <- es if continue) yield {
        val se = rec(e, soFar)
        if(se == BooleanLiteral(true)) continue = false
        soFar = register(Not(se), soFar)
        se
      }).copiedFrom(e)

      if (continue) {
        r
      } else {
        BooleanLiteral(true).copiedFrom(e)
      }

    case b if b.getType == BooleanType && impliedBy(b, path) =>
      BooleanLiteral(true).copiedFrom(b)

    case b if b.getType == BooleanType && contradictedBy(b, path) =>
      BooleanLiteral(false).copiedFrom(b)

    case _ =>
      super.rec(e, path)
  }
}
