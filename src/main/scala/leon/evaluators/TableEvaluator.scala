/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.ExprOps._
import purescala.TypeOps._
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

    classOf[IntLiteral] -> {
      (expr, rctx, gctx) =>
        expr
    },

    classOf[CharLiteral] -> {
      (expr, rctx, gctx) =>
        expr
    },

    classOf[UnitLiteral] -> {
      (expr, rctx, gctx) =>
        expr
    },

    classOf[FractionalLiteral] -> {
      (expr, rctx, gctx) =>
        normalizeFraction(expr.asInstanceOf[FractionalLiteral])
    },

    classOf[StringLiteral] -> {
      (expr, rctx, gctx) =>
        expr
    },

    classOf[GreaterEquals] -> {
      (expr, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val lt = expr.asInstanceOf[GreaterEquals]
        import lt._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 >= i2)
          case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
            val FractionalLiteral(n, _) = e(RealMinus(a, b))
            BooleanLiteral(n >= 0)
          case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 >= c2)
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
    },

    classOf[Application] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Application]
        import expr._
        e(callee) match {
          case l@Lambda(params, body) =>
            val newArgs = args.map(e)
            val mapping = l.paramSubst(newArgs)
            e(body)(rctx.withNewVars(mapping), gctx)
          case FiniteLambda(mapping, dflt, _) =>
            mapping.find { case (pargs, res) =>
              (args zip pargs).forall(p => e(Equals(p._1, p._2)) == BooleanLiteral(true))
            }.map(_._2).getOrElse(dflt)
          case f =>
            throw EvalError("Cannot apply non-lambda function " + f.asString)
        }

    },

    classOf[Tuple] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Tuple]
        Tuple(expr.exprs map e)
    },

    classOf[TupleSelect] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[TupleSelect]
        val Tuple(rs) = e(expr.tuple)
        rs(expr.index-1)
    },

    classOf[Let] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Let]
        import expr._
        val first = e(value)
        e(body)(rctx.withNewVar(binder, first), gctx)
    },
    classOf[Assert] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Assert]
        import expr._
        e(IfExpr(Not(pred), Error(expr.getType, error.getOrElse("Assertion failed @"+expr.getPos)), body))
    },
    classOf[Ensuring] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Ensuring]
        e(expr.toAssert)
    },
    classOf[Error] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Error]
        throw RuntimeError(s"Error reached in evaluation: ${expr.description}")
    },
    classOf[FunctionInvocation] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[FunctionInvocation]
        import expr._
        if (gctx.stepsLeft < 0) {
          throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
        }
        gctx.stepsLeft -= 1

        val evArgs = args map e

        //println(s"calling ${tfd.id} with $evArgs")

        // build a mapping for the function...
        val frame = rctx.withNewVars(tfd.paramSubst(evArgs))

        if(tfd.hasPrecondition) {
          e(tfd.precondition.get)(frame, gctx) match {
            case BooleanLiteral(true) =>
            case BooleanLiteral(false) =>
              throw RuntimeError("Precondition violation for " + tfd.id.asString + " reached in evaluation.: " + tfd.precondition.get.asString)
            case other =>
              throw RuntimeError(typeErrorMsg(other, BooleanType))
          }
        }

        val callResult = if (tfd.fd.annotations("extern") && ctx.classDir.isDefined) {
          scalaEv.call(tfd, evArgs)
        } else {
          if(!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) {
            throw EvalError("Evaluation of function with unknown implementation." + expr)
          }

          val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
          e(body)(frame, gctx)
        }

        //println(s"Gave $callResult")

        tfd.postcondition match  {
          case Some(post) =>
            e(application(post, Seq(callResult)))(frame, gctx) match {
              case BooleanLiteral(true) =>
              case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + tfd.id.asString + " reached in evaluation.")
              case other => throw EvalError(typeErrorMsg(other, BooleanType))
            }
          case None =>
        }

        callResult
    },
    classOf[Not] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Not]
        e(expr.expr) match {
          case BooleanLiteral(v) => BooleanLiteral(!v)
          case other => throw EvalError(typeErrorMsg(other, BooleanType))
        }
    },
    classOf[Implies] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Implies]
        import expr._
        e(lhs) match {
          case BooleanLiteral(false) => BooleanLiteral(true)
          case BooleanLiteral(true) => e(rhs)
          case le => throw EvalError(typeErrorMsg(le, BooleanType))
        }

    },
    classOf[Equals] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Equals]
        import expr._
        (e(lhs), e(rhs)) match {
          case (FiniteSet(el1, _),FiniteSet(el2, _)) => BooleanLiteral(el1 == el2)
          case (FiniteBag(el1, _),FiniteBag(el2, _)) => BooleanLiteral(el1 == el2)
          case (FiniteMap(el1, _, _),FiniteMap(el2, _, _)) => BooleanLiteral(el1.toSet == el2.toSet)
          case (FiniteLambda(m1, d1, _), FiniteLambda(m2, d2, _)) => BooleanLiteral(m1.toSet == m2.toSet && d1 == d2)
          case (lv, rv) => BooleanLiteral(lv == rv)
        }
    },
    classOf[CaseClass] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[CaseClass]
        import expr._
        val cc = CaseClass(ct, args.map(e))
        val check = bank.invariantCheck(cc)
        if (check.isFailure) {
          throw RuntimeError(
            "ADT invariant violation for " +
            ct.classDef.id.asString + " reached in evaluation.: " +
            ct.invariant.get.asString
          )
        } else if (check.isRequired) {
          e(FunctionInvocation(ct.invariant.get, Seq(cc))) match {
            case BooleanLiteral(success) =>
              bank.invariantResult(cc, success)
              if (!success)
                throw RuntimeError(
                  "ADT invariant violation for " +
                    ct.classDef.id.asString + " reached in evaluation.: " +
                    ct.invariant.get.asString
                )
            case other =>
              throw RuntimeError(typeErrorMsg(other, BooleanType))
          }
        }
        cc
    },
    classOf[AsInstanceOf] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[AsInstanceOf]
        val le = e(expr.expr)
        if (isSubtypeOf(le.getType, expr.tpe)) {
          le
        } else {
          throw RuntimeError("Cast error: cannot cast "+le.asString+" to "+expr.tpe.asString)
        }
    },
    classOf[IsInstanceOf] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[IsInstanceOf]
        val le = e(expr.expr)
        BooleanLiteral(isSubtypeOf(le.getType, expr.classType))
    },
    classOf[CaseClassSelector] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[CaseClassSelector]
        import expr._
        val le = e(caseClass)
        le match {
          case CaseClass(ct2, args) if classType == ct2 => args(classType.classDef.selectorID2Index(selector))
          case _ => throw EvalError(typeErrorMsg(le, classType))
        }
    },
    classOf[RealPlus] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[RealPlus]
        import expr._
        (e(lhs), e(rhs)) match {
          case (FractionalLiteral(ln, ld), FractionalLiteral(rn, rd)) =>
            normalizeFraction(FractionalLiteral(ln * rd + rn * ld, ld * rd))
          case (le, re) => throw EvalError(typeErrorMsg(le, RealType))
        }
    },
    classOf[RealMinus] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[RealMinus]
        import expr._
        e(RealPlus(lhs, RealUMinus(rhs)))
    },

    classOf[BVPlus] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVPlus]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },

    classOf[BVMinus] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVMinus]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },
    classOf[UMinus] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[UMinus]
        e(expr.expr) match {
          case InfiniteIntegerLiteral(i) => InfiniteIntegerLiteral(-i)
          case re => throw EvalError(typeErrorMsg(re, IntegerType))
        }
    },
    classOf[BVUMinus] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVUMinus]
        e(expr.expr) match {
          case IntLiteral(i) => IntLiteral(-i)
          case re => throw EvalError(typeErrorMsg(re, Int32Type))
        }
    },
    classOf[RealUMinus] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[RealUMinus]
        e(expr.expr) match {
          case FractionalLiteral(n, d) => FractionalLiteral(-n, d)
          case re => throw EvalError(typeErrorMsg(re, RealType))
        }
    },
    classOf[BVNot] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVNot]
        e(expr.expr) match {
          case IntLiteral(i) => IntLiteral(~i)
          case re => throw EvalError(typeErrorMsg(re, Int32Type))
        }
    },
    classOf[Times] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Times]
        import expr._
        (e(lhs), e(rhs)) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 * i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
        }
    },


    classOf[Division] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Division]
        import expr._
        (e(lhs), e(rhs)) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) =>
            if(i2 != BigInt(0)) InfiniteIntegerLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
          case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
        }
    },

    classOf[Remainder] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Remainder]
        import expr._
        (e(lhs), e(rhs)) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) =>
            if(i2 != BigInt(0)) InfiniteIntegerLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
          case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
        }
    },

    classOf[Modulo] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Modulo]
        import expr._
        (e(lhs), e(rhs)) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) =>
            if(i2 < 0)
              InfiniteIntegerLiteral(i1 mod (-i2))
            else if(i2 != BigInt(0))
              InfiniteIntegerLiteral(i1 mod i2)
            else
              throw RuntimeError("Modulo of division by 0.")
          case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
        }
    },
    classOf[Remainder] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Remainder]
        import expr._
        (e(lhs), e(rhs)) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) =>
            if(i2 != BigInt(0)) InfiniteIntegerLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
          case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
        }
    },
    classOf[BVTimes] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVTimes]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },
    classOf[BVDivision] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVDivision]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) =>
            if(i2 != 0) IntLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },

    classOf[BVRemainder] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVRemainder]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) =>
            if(i2 != 0) IntLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },
    classOf[RealTimes] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[RealTimes]
        import expr._
        (e(lhs), e(rhs)) match {
          case (FractionalLiteral(ln, ld), FractionalLiteral(rn, rd)) =>
            normalizeFraction(FractionalLiteral(ln * rn, ld * rd))
          case (le,re) => throw EvalError(typeErrorMsg(le, RealType))
        }
    },
    classOf[RealDivision] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[RealDivision]
        import expr._
        (e(lhs), e(rhs)) match {
          case (FractionalLiteral(ln, ld), FractionalLiteral(rn, rd)) =>
            if (rn != 0)
              normalizeFraction(FractionalLiteral(ln * rd, ld * rn))
            else throw RuntimeError("Division by 0.")
          case (le,re) => throw EvalError(typeErrorMsg(le, RealType))
        }
    },
    classOf[BVAnd] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVAnd]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 & i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },
    classOf[BVOr] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVOr]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 | i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },
    classOf[BVXOr] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVXOr]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 ^ i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },

    classOf[BVShiftLeft] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVShiftLeft]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 << i2)
          case (le, re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },

    classOf[BVAShiftRight] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVAShiftRight]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 >> i2)
          case (le, re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },
    classOf[BVLShiftRight] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[BVLShiftRight]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 >>> i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
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

    classOf[GreaterThan] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[GreaterThan]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 > i2)
          case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
            val FractionalLiteral(n, _) = e(RealMinus(a, b))
            BooleanLiteral(n > 0)
          case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 > c2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },
    classOf[LessEquals] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[LessEquals]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 <= i2)
          case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
            val FractionalLiteral(n, _) = e(RealMinus(a, b))
            BooleanLiteral(n <= 0)
          case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 <= c2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },
    classOf[GreaterEquals] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[GreaterEquals]
        import expr._
        (e(lhs), e(rhs)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 >= i2)
          case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
            val FractionalLiteral(n, _) = e(RealMinus(a, b))
            BooleanLiteral(n >= 0)
          case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 >= c2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
    },
    classOf[SetAdd] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[SetAdd]
        import expr._
        (e(set), e(elem)) match {
          case (FiniteSet(els1, tpe), evElem) => FiniteSet(els1 + evElem, tpe)
          case (le, re) => throw EvalError(typeErrorMsg(le, set.getType))
        }
    },

    classOf[SetIntersection] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[SetIntersection]
        import expr._
        (e(set1), e(set2)) match {
          case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => FiniteSet(els1 intersect els2, tpe)
          case (le,re) => throw EvalError(typeErrorMsg(le, set1.getType))
        }
    },

    classOf[SetDifference] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[SetDifference]
        import expr._
        (e(set1), e(set2)) match {
          case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => FiniteSet(els1 -- els2, tpe)
          case (le,re) => throw EvalError(typeErrorMsg(le, set1.getType))
        }
    },

    classOf[ElementOfSet] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[ElementOfSet]
        import expr._
        (e(element), e(set)) match {
          case (e, FiniteSet(els, _)) => BooleanLiteral(els.contains(e))
          case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
        }
    },

    classOf[SubsetOf] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[SubsetOf]
        import expr._
        (e(set1), e(set2)) match {
          case (FiniteSet(els1, _),FiniteSet(els2, _)) => BooleanLiteral(els1.subsetOf(els2))
          case (le,re) => throw EvalError(typeErrorMsg(le, set1.getType))
        }
    },

    classOf[SetCardinality] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[SetCardinality]
        e(expr.set) match {
          case FiniteSet(els, _) => InfiniteIntegerLiteral(els.size)
          case other => throw EvalError(typeErrorMsg(other, SetType(Untyped)))
        }
    },
    classOf[FiniteSet] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[FiniteSet]
        import expr._
        FiniteSet(elements map e, base)
    },

    classOf[Lambda] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val l = ex.asInstanceOf[Lambda]
        val mapping = variablesOf(l).map(id => id -> e(Variable(id))).toMap
        replaceFromIDs(mapping, l).asInstanceOf[Lambda]
    },
    classOf[FiniteLambda] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[FiniteLambda]
        import expr._
        FiniteLambda(mapping.map(p => p._1.map(e) -> e(p._2)), e(default), tpe)
    },
    classOf[Passes] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[Passes]
        e(expr.asConstraint)
    },

    classOf[MatchExpr] -> {
      (ex, rctx, gctx) =>
        implicit val r = rctx
        implicit val g = gctx
        val expr = ex.asInstanceOf[MatchExpr]
        import expr._
        val rscrut = e(scrutinee)
        cases.toStream.map(c => matchesCase(rscrut, c)).find(_.nonEmpty) match {
          case Some(Some((c, mappings))) =>
            e(c.rhs)(rctx.withNewVars(mappings), gctx)
          case _ =>
            throw RuntimeError("MatchError: "+rscrut.asString+" did not match any of the cases:\n"+cases)
        }
    },
    
    classOf[synthesis.utils.MutableExpr] -> {
      (ex, rctx, gctx) =>
        e(ex.asInstanceOf[synthesis.utils.MutableExpr].underlying)(rctx, gctx)
    }

    // TODO: Strings, bags, arrays, maps, forall

  )

  override protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    table.get(expr.getClass).map(_(expr, rctx, gctx)).getOrElse(super.e(expr))
  }

}
