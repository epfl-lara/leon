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

  val table: Map[Class[_], (Expr, RC, GC) => Expr] = Map(
    classOf[ExpansionExpr[_]] -> {
      (expr, rctx, gctx) => expr.asInstanceOf[ExpansionExpr[_]] match {
        case ExpansionExpr(NonTerminalInstance(_), typeTree) => expr
        case ExpansionExpr(ProdRuleInstance(nt, rule, children), typeTree) =>
          val childExprs = children.map(child => ExpansionExpr(child, Untyped))
          e(rule.builder(childExprs))(rctx, gctx)
      }
    },

    classOf[IfExpr] -> {
      (expr, rctx, gctx) => expr.asInstanceOf[IfExpr] match {
        case IfExpr(cond, thenn, elze) =>
          e(cond)(rctx, gctx) match {
            case BooleanLiteral(true) => e(thenn)(rctx, gctx)
            case BooleanLiteral(false) => e(elze)(rctx, gctx)
            case _ =>
              val ethenn = e(thenn)(rctx, gctx)
              val eelze = e(elze)(rctx, gctx)
              if (ethenn == eelze) ethenn else expr
          }
      }
    },

    classOf[And] -> {
      (expr, rctx, gctx) => expr.asInstanceOf[And] match {
        case And(exprs) =>
          implicit val rc = rctx
          implicit val gc = gctx
          val ee = exprs.map(e)
          if (ee.contains(BooleanLiteral(false))) {
            BooleanLiteral(false)
          } else if (ee.forall(_ == BooleanLiteral(true))) {
            BooleanLiteral(true)
          } else {
            expr
          }
      }
    },

    classOf[Or] -> {
      (expr, rctx, gctx) => expr.asInstanceOf[Or] match {
        case Or(exprs) =>
          implicit val rc = rctx
          implicit val gc = gctx
          val ee = exprs.map(e)
          if (ee.contains(BooleanLiteral(true))) {
            BooleanLiteral(true)
          } else if (ee.forall(_ == BooleanLiteral(false))) {
            BooleanLiteral(false)
          } else {
            expr
          }
      }
    },

    classOf[Implies] -> {
      (expr, rctx, gctx) => expr.asInstanceOf[Implies] match {
        case Implies(lhs, rhs) =>
          val elhs = e(lhs)(rctx, gctx)
          val erhs = e(rhs)(rctx, gctx)
          if (elhs == BooleanLiteral(false) || erhs == BooleanLiteral(true) || elhs == erhs) {
            BooleanLiteral(true)
          } else {
            expr
          }
      }
    },

    classOf[Equals] -> {
      (expr, rctx, gctx) => expr.asInstanceOf[Equals] match {
        case Equals(le, re) =>
          val lv = e(le)(rctx, gctx)
          val rv = e(re)(rctx, gctx)

          if (lv == rv) {
            BooleanLiteral(true)
          } else {
            (lv, rv) match {
              case (FiniteSet(el1, _),FiniteSet(el2, _)) => BooleanLiteral(el1 == el2)
              case (FiniteBag(el1, _),FiniteBag(el2, _)) => BooleanLiteral(el1 == el2)
              case (FiniteMap(el1, _, _),FiniteMap(el2, _, _)) => BooleanLiteral(el1.toSet == el2.toSet)
              case (FiniteLambda(m1, d1, _), FiniteLambda(m2, d2, _)) => BooleanLiteral(m1.toSet == m2.toSet && d1 == d2)
              case (ExpansionExpr(_, _), _) => expr
              case (_, ExpansionExpr(_, _)) => expr
              case _ => BooleanLiteral(false)
            }
          }
      }
    },

    classOf[Plus] -> {
      (expr, rctx, gctx) => expr.asInstanceOf[Plus] match {
        case Plus(l, r) =>
          val el = e(l)(rctx, gctx)
          val er = e(r)(rctx, gctx)

          (el, er) match {
            case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 + i2)
            case (InfiniteIntegerLiteral(i1), _) if i1 == BigInt(0) => er
            case (_, InfiniteIntegerLiteral(i2)) if i2 == BigInt(0) => el
            case _ => expr
          }
      }
    },

    classOf[Minus] -> {
      (expr, rctx, gctx) => expr.asInstanceOf[Plus] match {
        case Plus(l, r) =>
          val el = e(l)(rctx, gctx)
          val er = e(r)(rctx, gctx)

          (el, er) match {
            case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 - i2)
            case (_, InfiniteIntegerLiteral(i2)) if i2 == BigInt(0) => el
            case _ => expr
          }
      }
    }
  )

  def defaultE(expr: Expr, rctx: RC, gctx: GC): Expr = {
    try {
      super.e(expr)(rctx, gctx)
    } catch {
      case evalError: EvalError => expr
    }
  }

  protected[evaluators] override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    table.getOrElse(expr.getClass, defaultE(_, _, _))(expr, rctx, gctx)
  }

}
