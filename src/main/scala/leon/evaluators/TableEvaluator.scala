/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Constructors._
import purescala.Expressions._
import purescala.Types._
import purescala.Definitions.Program
import scala.collection.immutable.HashMap


class TableEvaluator(ctx: LeonContext, prog: Program, bank: EvaluationBank = new EvaluationBank) extends DefaultEvaluator(ctx, prog, bank) {

  private val table: HashMap[Class[_], (Expr, RC, GC) => Expr] = HashMap(
    classOf[Variable] -> {
      (expr, rctx, gctx) =>
        val v = expr.asInstanceOf[Variable]
        rctx.mappings.get(v.id) match {
          case Some(v) =>
            v
          case None =>
            throw EvalError("No value for identifier " + v.id.asString + " in mapping " + rctx.mappings)
        }
    },

    classOf[IfExpr] -> {
      (expr, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val ite = expr.asInstanceOf[IfExpr]
        import ite._

        val first = e(cond)
        first match {
          case BooleanLiteral(true) => e(thenn)
          case BooleanLiteral(false) => e(elze)
          case _ => throw EvalError(typeErrorMsg(first, BooleanType))
        }
    },

    classOf[InfiniteIntegerLiteral] -> {
      (expr, rctx, gctx) =>
        expr
    },

    classOf[BooleanLiteral] -> {
      (expr, rctx, gctx) =>
        expr
    },

    classOf[LessThan] -> {
      (expr, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val lt = expr.asInstanceOf[LessThan]
        import lt._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 < i2)
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 < i2)
          case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
            val FractionalLiteral(n, _) = e(RealMinus(a, b))
            BooleanLiteral(n < 0)
          case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 < c2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },

    classOf[And] -> {
      (expr, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val args = expr.asInstanceOf[And].exprs
        if (args.isEmpty) BooleanLiteral(true)
        else {
          e(args.head) match {
            case BooleanLiteral(false) => BooleanLiteral(false)
            case BooleanLiteral(true) => e(andJoin(args.tail))
            case other => throw EvalError(typeErrorMsg(other, BooleanType))
          }
        }
    },

    classOf[Or] -> {
      (expr, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val args = expr.asInstanceOf[Or].exprs
        if (args.isEmpty) BooleanLiteral(false)
        else {
          e(args.head) match {
            case BooleanLiteral(true) => BooleanLiteral(true)
            case BooleanLiteral(false) => e(orJoin(args.tail))
            case other => throw EvalError(typeErrorMsg(other, BooleanType))
          }
        }
    },

    classOf[Plus] -> {
      (expr, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val pl = expr.asInstanceOf[Plus]
        import pl._
        (e(lhs), e(rhs)) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 + i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
        }
    },

    classOf[Minus] -> {
      (expr, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val m = expr.asInstanceOf[Minus]
        import m._
        (e(lhs), e(rhs)) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 - i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
        }
    }

  )

  override protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    table.get(expr.getClass).map(_(expr, rctx, gctx)).getOrElse(super.e(expr))
  }

}