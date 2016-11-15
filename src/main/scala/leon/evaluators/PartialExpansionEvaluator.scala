package leon
package evaluators

import leon.grammars.{ExpansionExpr, NonTerminalInstance, ProdRuleInstance}
import leon.purescala.Definitions.Program
import leon.purescala.Expressions._
import leon.purescala.Types.Untyped

// The following code has been grafted together from DefaultEvaluator and RecursiveEvaluator.

class PartialExpansionEvaluator(ctx: LeonContext, prog: Program, bank: EvaluationBank = new EvaluationBank)
  extends RecursiveEvaluator(ctx, prog, bank, 50000)
    with HasDefaultGlobalContext
    with HasDefaultRecContext {

  protected[evaluators] override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    // println(s"> Evalling ${expr}")
    val ans = expr match {
      case Equals(le, re) => {
        // println("Evalling equals")
        val lv = e(le)
        val rv = e(re)

        val ans = if (lv == rv) {
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
        // println(s"${ans}")
        ans
      }

      case ExpansionExpr(NonTerminalInstance(_), typeTree) => {
        // println("Immediate return!")
        expr
      }

      case ExpansionExpr(ProdRuleInstance(nt, rule, children), typeTree) => {
        val childResults = children.map(child => e(ExpansionExpr(child, Untyped)))
        if (childResults.exists(_.isInstanceOf[ExpansionExpr[_]])) {
          // println("This call!")
          partialE(rule.builder(childResults), expr)
        } else {
          // println(s">> Super call 1! expr: ${expr}")
          try {
            val ans = super.e(rule.builder(childResults))
            // println(s"<< Super call 1! expr: ${expr}. Ans: ${ans}")
            ans
          } catch {
            case evalError: EvalError => {
              // println(s"EvalError: ${evalError}")
              // println(s"<< Failed super call 1: ${expr}")
              expr
            }
          }
        }
      }

      case _ => {
        // println(s">> Super call 2! expr: ${expr}")
        try {
          val ans = super.e(expr)
          // println(s"<< Super call 2! expr: ${expr}. Ans: ${ans}")
          ans
        } catch {
          case evalError: EvalError => {
            // println(s"EvalError: ${evalError}")
            // println(s"<< Failed super call 2: ${expr}")
            expr
          }
        }
      }
    }
    // println(s"< Finished evalling ${expr}. Producing result: ${ans}")
    ans
  }

  def partialE(expr: Expr, fallback: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case And(exprs) => {
      val ee = exprs.map(e)
      if (ee.contains(BooleanLiteral(false))) {
        BooleanLiteral(false)
      } else if (ee.forall(_ == BooleanLiteral(true))) {
        BooleanLiteral(true)
      } else {
        fallback
      }
    }

    case Or(exprs) => {
      val ee = exprs.map(e)
      if (ee.contains(BooleanLiteral(true))) {
        BooleanLiteral(true)
      } else if (ee.forall(_ == BooleanLiteral(false))) {
        BooleanLiteral(false)
      } else {
        fallback
      }
    }

    case Implies(lhs, rhs) => {
      val elhs = e(lhs)
      val erhs = e(rhs)
      if (elhs == BooleanLiteral(false) || erhs == BooleanLiteral(true) || elhs == erhs) {
        BooleanLiteral(true)
      } else {
        fallback
      }
    }

    case IfExpr(cond, thenn, elze) => {
      val econd = e(cond)
      val ethenn = e(thenn)
      val eelze = e(elze)
      if (econd == BooleanLiteral(true)) {
        ethenn
      } else if (econd == BooleanLiteral(false)) {
        eelze
      } else if (ethenn == eelze) {
        ethenn
      } else {
        fallback
      }
    }

    case _ => fallback
  }

}
