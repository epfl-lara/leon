package leon
package evaluators

import leon.grammars.{ExpansionExpr, NonTerminalInstance, ProdRuleInstance}
import leon.purescala.Definitions.Program
import leon.purescala.Expressions._
import leon.purescala.Types.Untyped

// The following code has been grafted together from DefaultEvaluator and RecursiveEvaluator.

class PartialExpansionEvaluator(ctx: LeonContext, prog: Program, bank: EvaluationBank = new EvaluationBank)
  extends TableEvaluator(ctx, prog, bank)
    with HasDefaultGlobalContext
    with HasDefaultRecContext {

  case class PERes(res: Expr, complete: Boolean)

  val table: Map[Class[_], (Expr, RC, GC) => PERes] = Map(
    classOf[ExpansionExpr[_]] -> {
      (expr, rctx, gctx) => expr.asInstanceOf[ExpansionExpr[_]] match {
        case ExpansionExpr(NonTerminalInstance(_), typeTree) => PERes(expr, complete = false)
        case ExpansionExpr(ProdRuleInstance(nt, rule, children), typeTree) =>
          val childExprs = children.map(child => ExpansionExpr(child, Untyped))
          val falseExpr = rule.builder(childExprs)
          pe(falseExpr)(rctx, gctx)
      }
    },

    classOf[IfExpr] -> {
      (expr, rctx, gctx) => {
        val IfExpr(cond, thenn, elze) = expr
        pe(cond)(rctx, gctx) match {
          case PERes(BooleanLiteral(true), true) => pe(thenn)(rctx, gctx)
          case PERes(BooleanLiteral(false), true) => pe(elze)(rctx, gctx)
          case _ => PERes(expr, complete = false)
        }
      }
    },

    classOf[And] -> {
      (expr, rctx, gctx) => {
        val And(exprs) = expr
        implicit val rc = rctx
        implicit val gc = gctx

        def pevalAnd(exprs: Seq[Expr], allTrue: Boolean = true): PERes = {
          if (exprs.isEmpty) PERes(BooleanLiteral(allTrue), complete = allTrue)
          else {
            val ehd = exprs.head
            val etl = exprs.tail
            pe(ehd) match {
              case PERes(BooleanLiteral(true), true) => pevalAnd(etl, allTrue)
              case PERes(BooleanLiteral(false), true) => PERes(BooleanLiteral(false), complete = true)
              case _ => pevalAnd(etl, allTrue = false)
            }
          }
        }

        pevalAnd(exprs)
      }
    },

    classOf[Or] -> {
      (expr, rctx, gctx) => {
        val Or(exprs) = expr
        implicit val rc = rctx
        implicit val gc = gctx

        def pevalOr(exprs: Seq[Expr], allFalse: Boolean = true): PERes = {
          if (exprs.isEmpty) PERes(BooleanLiteral(!allFalse), complete = allFalse)
          else {
            val ehd = exprs.head
            val etl = exprs.tail
            pe(ehd) match {
              case PERes(BooleanLiteral(true), true) => PERes(BooleanLiteral(true), complete = true)
              case PERes(BooleanLiteral(false), true) => pevalOr(etl, allFalse)
              case _ => pevalOr(etl, allFalse = false)
            }
          }
        }

        pevalOr(exprs)
      }
    },

    classOf[Implies] -> {
      (expr, rctx, gctx) => {
        val Implies(lhs, rhs) = expr
        pe(lhs)(rctx, gctx) match {
          case PERes(BooleanLiteral(true), true) => pe(rhs)(rctx, gctx)
          case PERes(BooleanLiteral(false), true) => PERes(BooleanLiteral(true), complete = true)
          case _ => pe(rhs)(rctx, gctx)
        }
      }
    },

    classOf[Equals] -> {
      (expr, rctx, gctx) => {
        val Equals(le, re) = expr
        val lv = pe(le)(rctx, gctx)
        val rv = pe(re)(rctx, gctx)

        (lv, rv) match {
          case (PERes(lve, true), PERes(rve, true)) => PERes(super.e(Equals(lve, rve))(rctx, gctx), complete = true)
          case _ => PERes(expr, complete = false)
        }
      }
    }
  )

  def defaultE(expr: Expr, rctx: RC, gctx: GC): PERes = {
    try {
      PERes(super.e(expr)(rctx, gctx), complete = true)
    } catch {
      case evalError: EvalError => PERes(expr, complete = false)
    }
  }

  def pe(expr: Expr)(implicit rctx: RC, gctx: GC): PERes = {
    table.getOrElse(expr.getClass, defaultE(_, _, _))(expr, rctx, gctx)
  }

  protected[evaluators] override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = pe(expr) match {
    case PERes(res, true) => res
    case PERes(_, false) => throw EvalError(s"Unable to fully evaluate expression ${expr}")
  }

}
