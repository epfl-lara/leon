/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Expressions._
import Types._
import ExprOps._
import Extractors._
import Constructors._
import solvers._

class SimplifierWithPaths(sf: SolverFactory[Solver], val initPath: Path = Path.empty) extends TransformerWithPC {

  val solver = SimpleSolverAPI(sf)

  def impliedBy(e: Expr, path: Path) : Boolean = try {
    solver.solveVALID(path implies e) match {
      case Some(true) => true
      case _ => false
    }
  } catch {
    case _ : Exception => false
  }

  def contradictedBy(e: Expr, path: Path) : Boolean = try {
    solver.solveVALID(path implies not(e)) match {
      case Some(true) => true
      case _ => false
    }
  } catch {
    case _ : Exception => false
  }

  def valid(e: Expr) : Boolean = try {
    solver.solveVALID(e) match {
      case Some(true) => true
      case _ => false 
    }
  } catch {
    case _ : Exception => false
  }

  def sat(e: Expr) : Boolean = try {
    solver.solveSAT(e) match {
      case (Some(false),_) => false
      case _ => true
    }
  } catch {
    case _ : Exception => true
  }

  protected override def rec(e: Expr, path: Path) = e match {
    case Require(pre, body) if impliedBy(pre, path) =>
      body

    case IfExpr(cond, thenn, _) if impliedBy(cond, path) =>
      rec(thenn, path)

    case IfExpr(cond, _, elze ) if contradictedBy(cond, path) =>
      rec(elze, path)

    case And(e +: _) if contradictedBy(e, path) =>
      BooleanLiteral(false).copiedFrom(e)

    case And(e +: es) if impliedBy(e, path) =>
      val remaining = if (es.size > 1) And(es).copiedFrom(e) else es.head
      rec(remaining, path)

    case Or(e +: _) if impliedBy(e, path) =>
      BooleanLiteral(true).copiedFrom(e)

    case Or(e +: es) if contradictedBy(e, path) =>
      val remaining = if (es.size > 1) Or(es).copiedFrom(e) else es.head
      rec(remaining, path)

    case Implies(lhs, rhs) if impliedBy(lhs, path) =>
      rec(rhs, path)

    case Implies(lhs, rhs) if contradictedBy(lhs, path) =>
      BooleanLiteral(true).copiedFrom(e)

    case me @ MatchExpr(scrut, cases) =>
      val rs = rec(scrut, path)

      var stillPossible = true

      val conds = matchExprCaseConditions(me, path)

      val newCases = cases.zip(conds).flatMap { case (cs, cond) =>
       if (stillPossible && sat(cond.toClause)) {

          if (valid(cond.toClause)) {
            stillPossible = false
          }

          Seq((cs match {
            case SimpleCase(p, rhs) =>
              SimpleCase(p, rec(rhs, cond))
            case GuardedCase(p, g, rhs) =>
              // @mk: This is quite a dirty hack. We just know matchCasePathConditions
              // returns the current guard as the last element.
              // We don't include it in the path condition when we recurse into itself.
              // @nv: baaaaaaaad!!!
              val condWithoutGuard = new Path(cond.elements.dropRight(1))
              val newGuard = rec(g, condWithoutGuard)
              if (valid(newGuard))
                SimpleCase(p, rec(rhs,cond))
              else 
                GuardedCase(p, newGuard, rec(rhs, cond))
          }).copiedFrom(cs))
        } else {
          Seq()
        }
      }

      newCases match {
        case List() =>
          Error(e.getType, "Unreachable code").copiedFrom(e)
        case _ =>
          matchExpr(rs, newCases).copiedFrom(e)
      }

    case a @ Assert(pred, _, body) if impliedBy(pred, path) =>
      body

    case a @ Assert(pred, msg, body) if contradictedBy(pred, path) =>
      Error(body.getType, s"Assertion failed: $msg").copiedFrom(a)

    case b if b.getType == BooleanType && impliedBy(b, path) =>
      BooleanLiteral(true).copiedFrom(b)

    case b if b.getType == BooleanType && contradictedBy(b, path) =>
      BooleanLiteral(false).copiedFrom(b)

    case _ =>
      super.rec(e, path)
  }
}
