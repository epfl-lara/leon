/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Quantification._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Expressions.Pattern
import purescala.Extractors._
import purescala.TypeOps.isSubtypeOf
import purescala.Types._
import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import solvers.TimeoutableSolverFactory
import solvers.{PartialModel, SolverFactory}
import purescala.DefOps
import solvers.{PartialModel, Model, SolverFactory, SolverContext}
import solvers.unrolling.UnrollingProcedure
import scala.collection.mutable.{Map => MutableMap}
import scala.concurrent.duration._
import org.apache.commons.lang3.StringEscapeUtils
import leon.purescala.TypeOps
/**
 * An evaluator for simple arithmetic/logical/datatype expressions.
 * This is used in the core engine of Orb, and needs to very efficient.
 * Caution: using default evaluator in place of this results in 10x slowdown in Orb.
 */
class OrbEvaluator(ctx: LeonContext, prog: Program) extends Evaluator(ctx, prog) {

  type Value = Expr

  protected implicit val _ = ctx

  val name = "LightweightOrbEvaluator"
  val description = "An optimized evaluator used to evaluate simple experssions generated during the invariant inference phase"

  def eval(ex: Expr, model: Model) = {
    try {
      EvaluationResults.Successful(recEval(ex)(model))
    } catch {
      case EvalError(msg) =>
        EvaluationResults.EvaluatorError(msg)
      case so: StackOverflowError =>
        EvaluationResults.RuntimeError("Stack overflow")
      case e @ RuntimeError(msg) =>
        EvaluationResults.RuntimeError(msg)
      case jre: java.lang.RuntimeException =>
        EvaluationResults.RuntimeError(jre.getMessage)
    } finally {
    }
  }

  override def compile(expr: Expr, args: Seq[Identifier]) : Option[Model => EvaluationResult] =
    throw new IllegalArgumentException("Not supported operation!")

  case class EvalError(msg : String) extends Exception {
    override def getMessage = msg + Option(super.getMessage).map("\n" + _).getOrElse("")
  }
  case class RuntimeError(msg : String) extends Exception

  def typeErrorMsg(tree : Expr, expected : TypeTree) : String = s"Type error : expected ${expected.asString}, found ${tree.asString} of type ${tree.getType}."

  protected[evaluators] def recEval(expr: Expr)(implicit mod: Model): Expr = expr match {
    case Variable(id) =>
      mod.get(id) match {
        case Some(v) => v
        case None =>
          throw EvalError("No value for identifier " + id.asString + " in mapping " + mod.toMap)
      }

    case Tuple(ts) =>
      val tsRec = ts.map(recEval)
      Tuple(tsRec)

    case TupleSelect(t, i) =>
      val Tuple(rs) = recEval(t)
      rs(i - 1)

    case IfExpr(cond, thenn, elze) =>
      val first = recEval(cond)
      first match {
        case BooleanLiteral(true) => recEval(thenn)
        case BooleanLiteral(false) => recEval(elze)
        case _ => throw EvalError(typeErrorMsg(first, BooleanType))
      }

    case And(args) if args.isEmpty => BooleanLiteral(true)
    case And(args) =>
      recEval(args.head) match {
        case BooleanLiteral(false) => BooleanLiteral(false)
        case BooleanLiteral(true) => recEval(andJoin(args.tail))
        case other => throw EvalError(typeErrorMsg(other, BooleanType))
      }

    case Or(args) if args.isEmpty => BooleanLiteral(false)
    case Or(args) =>
      recEval(args.head) match {
        case BooleanLiteral(true) => BooleanLiteral(true)
        case BooleanLiteral(false) => recEval(orJoin(args.tail))
        case other => throw EvalError(typeErrorMsg(other, BooleanType))
      }

    case Not(arg) =>
      recEval(arg) match {
        case BooleanLiteral(v) => BooleanLiteral(!v)
        case other => throw EvalError(typeErrorMsg(other, BooleanType))
      }

    case Implies(l,r) =>
      recEval(l) match {
        case BooleanLiteral(false) => BooleanLiteral(true)
        case BooleanLiteral(true) => recEval(r)
        case le => throw EvalError(typeErrorMsg(le, BooleanType))
      }

    case Equals(le,re) =>
      val lv = recEval(le)
      val rv = recEval(re)

      (lv,rv) match {
        case (FiniteSet(el1, _),FiniteSet(el2, _)) => BooleanLiteral(el1 == el2)
        case (FiniteBag(el1, _),FiniteBag(el2, _)) => BooleanLiteral(el1 == el2)
        case (FiniteMap(el1, _, _),FiniteMap(el2, _, _)) => BooleanLiteral(el1.toSet == el2.toSet)
        case (FiniteLambda(m1, d1, _), FiniteLambda(m2, d2, _)) => BooleanLiteral(m1.toSet == m2.toSet && d1 == d2)
        case _ => BooleanLiteral(lv == rv)
      }

    case CaseClass(cct, args) => CaseClass(cct, args.map(recEval))

    case AsInstanceOf(expr, ct) =>
      val le = recEval(expr)
      if (isSubtypeOf(le.getType, ct)) {
        le
      } else {
        throw RuntimeError("Cast error: cannot cast "+le.asString+" to "+ct.asString)
      }

    case IsInstanceOf(expr, ct) =>
      val le = recEval(expr)
      BooleanLiteral(isSubtypeOf(le.getType, ct))

    case CaseClassSelector(ct1, expr, sel) =>
      val le = recEval(expr)
      le match {
        case CaseClass(ct2, args) if ct1 == ct2 => args(ct1.classDef.selectorID2Index(sel))
        case _ => throw EvalError(typeErrorMsg(le, ct1))
      }

    case Plus(l,r) =>
      (recEval(l), recEval(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 + i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }

    case Minus(l,r) =>
      (recEval(l), recEval(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 - i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }

    case RealPlus(l, r) =>
      (recEval(l), recEval(r)) match {
        case (FractionalLiteral(ln, ld), FractionalLiteral(rn, rd)) =>
          normalizeFraction(FractionalLiteral(ln * rd + rn * ld, ld * rd))
        case (le, re) => throw EvalError(typeErrorMsg(le, RealType))
      }

    case RealMinus(l,r) =>
      recEval(RealPlus(l, RealUMinus(r)))

    case StringConcat(l, r) =>
      (recEval(l), recEval(r)) match {
        case (StringLiteral(i1), StringLiteral(i2)) => StringLiteral(i1 + i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, StringType))
      }
    case StringLength(a) => recEval(a) match {
      case StringLiteral(a) => IntLiteral(a.length)
      case res => throw EvalError(typeErrorMsg(res, Int32Type))
    }
    case StringBigLength(a) => recEval(a) match {
      case StringLiteral(a) => InfiniteIntegerLiteral(a.length)
      case res => throw EvalError(typeErrorMsg(res, IntegerType))
    }
    case SubString(a, start, end) => (recEval(a), recEval(start), recEval(end)) match {
      case (StringLiteral(a), IntLiteral(b), IntLiteral(c))  =>
        StringLiteral(a.substring(b, c))
      case res => throw EvalError(typeErrorMsg(res._1, StringType))
    }
    case BigSubString(a, start, end) => (recEval(a), recEval(start), recEval(end)) match {
      case (StringLiteral(a), InfiniteIntegerLiteral(b), InfiniteIntegerLiteral(c))  =>
        StringLiteral(a.substring(b.toInt, c.toInt))
      case res => throw EvalError(typeErrorMsg(res._1, StringType))
    }
    case Int32ToString(a) => recEval(a) match {
      case IntLiteral(i) => StringLiteral(i.toString)
      case res =>  throw EvalError(typeErrorMsg(res, Int32Type))
    }
    case CharToString(a) =>
      recEval(a) match {
        case CharLiteral(i) => StringLiteral(i.toString)
        case res =>  throw EvalError(typeErrorMsg(res, CharType))
      }
    case IntegerToString(a) => recEval(a) match {
        case InfiniteIntegerLiteral(i) => StringLiteral(i.toString)
        case res =>  throw EvalError(typeErrorMsg(res, IntegerType))
      }
    case BooleanToString(a) => recEval(a) match {
        case BooleanLiteral(i) => StringLiteral(i.toString)
        case res =>  throw EvalError(typeErrorMsg(res, BooleanType))
      }
    case RealToString(a) => recEval(a) match {
        case FractionalLiteral(n, d) => StringLiteral(n.toString + "/" + d.toString)
        case res =>  throw EvalError(typeErrorMsg(res, RealType))
      }

    case BVWideningCast(a, Int32Type) =>
      recEval(a) match {
        case ByteLiteral(b) => IntLiteral(b.toInt)
        case x => throw EvalError(s"Expected an integral type (e.g. Int8Type) but got $x of type ${x.getType}")
      }

    case BVNarrowingCast(a, Int8Type) =>
      recEval(a) match {
        case IntLiteral(i) => ByteLiteral(i.toByte)
        case x => throw EvalError(s"Expected an integral type (e.g. Int32Type) but got $x of type ${x.getType}")
      }

    case BVPlus(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVMinus(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case UMinus(ex) =>
      recEval(ex) match {
        case InfiniteIntegerLiteral(i) => InfiniteIntegerLiteral(-i)
        case re => throw EvalError(typeErrorMsg(re, IntegerType))
      }

    case BVUMinus(ex) =>
      recEval(ex) match {
        case IntLiteral(i) => IntLiteral(-i)
        case re => throw EvalError(typeErrorMsg(re, Int32Type))
      }

    case RealUMinus(ex) =>
      recEval(ex) match {
        case FractionalLiteral(n, d) => FractionalLiteral(-n, d)
        case re => throw EvalError(typeErrorMsg(re, RealType))
      }


    case BVNot(ex) =>
      recEval(ex) match {
        case IntLiteral(i) => IntLiteral(~i)
        case re => throw EvalError(typeErrorMsg(re, Int32Type))
      }

    case Times(l,r) =>
      (recEval(l), recEval(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 * i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }

    case Division(l,r) =>
      (recEval(l), recEval(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) =>
          if(i2 != BigInt(0)) InfiniteIntegerLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }

    case Remainder(l,r) =>
      (recEval(l), recEval(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) =>
          if(i2 != BigInt(0)) InfiniteIntegerLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }
    case Modulo(l,r) =>
      (recEval(l), recEval(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) =>
          if(i2 < 0)
            InfiniteIntegerLiteral(i1 mod (-i2))
          else if(i2 != BigInt(0))
            InfiniteIntegerLiteral(i1 mod i2)
          else
            throw RuntimeError("Modulo of division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }

    case BVTimes(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVDivision(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) =>
          if(i2 != 0) IntLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVRemainder(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) =>
          if(i2 != 0) IntLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case RealTimes(l,r) =>
      (recEval(l), recEval(r)) match {
        case (FractionalLiteral(ln, ld), FractionalLiteral(rn, rd)) =>
          normalizeFraction(FractionalLiteral((ln * rn), (ld * rd)))
        case (le,re) => throw EvalError(typeErrorMsg(le, RealType))
      }

    case RealDivision(l,r) =>
      (recEval(l), recEval(r)) match {
        case (FractionalLiteral(ln, ld), FractionalLiteral(rn, rd)) =>
          if (rn != 0)
            normalizeFraction(FractionalLiteral(ln * rd, ld * rn))
          else throw RuntimeError("Division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, RealType))
      }


    case BVAnd(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 & i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVOr(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 | i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVXOr(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 ^ i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVShiftLeft(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 << i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVAShiftRight(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 >> i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVLShiftRight(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 >>> i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case LessThan(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 < i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 < i2)
        case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = recEval(RealMinus(a, b))
          BooleanLiteral(n < 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 < c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case GreaterThan(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = recEval(RealMinus(a, b))
          BooleanLiteral(n > 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 > c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case LessEquals(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = recEval(RealMinus(a, b))
          BooleanLiteral(n <= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 <= c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case GreaterEquals(l,r) =>
      (recEval(l), recEval(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = recEval(RealMinus(a, b))
          BooleanLiteral(n >= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 >= c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case SetAdd(s1, elem) =>
      (recEval(s1), recEval(elem)) match {
        case (FiniteSet(els1, tpe), evElem) => FiniteSet(els1 + evElem, tpe)
        case (le, re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetUnion(s1,s2) =>
      (recEval(s1), recEval(s2)) match {
        case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => FiniteSet(els1 ++ els2, tpe)
        case (le, re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetIntersection(s1,s2) =>
      (recEval(s1), recEval(s2)) match {
        case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => FiniteSet(els1 intersect els2, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetDifference(s1,s2) =>
      (recEval(s1), recEval(s2)) match {
        case (FiniteSet(els1, tpe), FiniteSet(els2, _)) => FiniteSet(els1 -- els2, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case ElementOfSet(el,s) => (recEval(el), recEval(s)) match {
      case (e, FiniteSet(els, _)) => BooleanLiteral(els.contains(e))
      case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
    }

    case SubsetOf(s1,s2) => (recEval(s1), recEval(s2)) match {
      case (FiniteSet(els1, _),FiniteSet(els2, _)) => BooleanLiteral(els1.subsetOf(els2))
      case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
    }

    case SetCardinality(s) =>
      val sr = recEval(s)
      sr match {
        case FiniteSet(els, _) => InfiniteIntegerLiteral(els.size)
        case _ => throw EvalError(typeErrorMsg(sr, SetType(Untyped)))
      }

    case f @ FiniteSet(els, base) =>
      FiniteSet(els.map(recEval), base)

    case BagAdd(bag, elem) => (recEval(bag), recEval(elem)) match {
      case (FiniteBag(els, tpe), evElem) => FiniteBag(els + (evElem -> (els.get(evElem) match {
        case Some(InfiniteIntegerLiteral(i)) => InfiniteIntegerLiteral(i + 1)
        case Some(i) => throw EvalError(typeErrorMsg(i, IntegerType))
        case None => InfiniteIntegerLiteral(1)
      })), tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, bag.getType))
    }

    case MultiplicityInBag(elem, bag) => (recEval(elem), recEval(bag)) match {
      case (evElem, FiniteBag(els, tpe)) => els.getOrElse(evElem, InfiniteIntegerLiteral(0))
      case (le, re) => throw EvalError(typeErrorMsg(re, bag.getType))
    }

    case BagIntersection(b1, b2) => (recEval(b1), recEval(b2)) match {
      case (FiniteBag(els1, tpe), FiniteBag(els2, _)) => FiniteBag(els1.flatMap { case (k, v) =>
        val i = (v, els2.getOrElse(k, InfiniteIntegerLiteral(0))) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => i1 min i2
          case (le, re) => throw EvalError(typeErrorMsg(le, IntegerType))
        }

        if (i <= 0) None else Some(k -> InfiniteIntegerLiteral(i))
      }, tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, b1.getType))
    }

    case BagUnion(b1, b2) => (recEval(b1), recEval(b2)) match {
      case (FiniteBag(els1, tpe), FiniteBag(els2, _)) => FiniteBag((els1.keys ++ els2.keys).toSet.map { (k: Expr) =>
        k -> ((els1.getOrElse(k, InfiniteIntegerLiteral(0)), els2.getOrElse(k, InfiniteIntegerLiteral(0))) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 + i2)
          case (le, re) => throw EvalError(typeErrorMsg(le, IntegerType))
        })
      }.toMap, tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, b1.getType))
    }

    case BagDifference(b1, b2) => (recEval(b1), recEval(b2)) match {
      case (FiniteBag(els1, tpe), FiniteBag(els2, _)) => FiniteBag(els1.flatMap { case (k, v) =>
        val i = (v, els2.getOrElse(k, InfiniteIntegerLiteral(0))) match {
          case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => i1 - i2
          case (le, re) => throw EvalError(typeErrorMsg(le, IntegerType))
        }

        if (i <= 0) None else Some(k -> InfiniteIntegerLiteral(i))
      }, tpe)

      case (le, re) => throw EvalError(typeErrorMsg(le, b1.getType))
    }

    case FiniteBag(els, base) =>
      FiniteBag(els.map{ case (k, v) => (recEval(k), recEval(v)) }, base)

    case ArrayLength(a) =>
      val FiniteArray(_, _, IntLiteral(length)) = recEval(a)
      IntLiteral(length)

    case ArrayUpdated(a, i, v) =>
      val ra = recEval(a)
      val ri = recEval(i)
      val rv = recEval(v)

      val IntLiteral(index) = ri
      val FiniteArray(elems, default, length) = ra
      val ArrayType(tp) = ra.getType
      finiteArray(elems.updated(index, rv), default map { (_, length) }, tp)

    case ArraySelect(a, i) =>
      val IntLiteral(index) = recEval(i)
      val FiniteArray(elems, default, _) = recEval(a)
      try {
        elems.get(index).orElse(default).get
      } catch {
        case e : IndexOutOfBoundsException => throw RuntimeError(e.getMessage)
      }

    case f @ FiniteArray(elems, default, length) =>
      val ArrayType(tp) = f.getType
      finiteArray(
        elems.map(el => (el._1, recEval(el._2))),
        default.map{ d => (recEval(d), recEval(length)) },
        tp
      )

    case f @ FiniteMap(ss, kT, vT) =>
      FiniteMap(ss.map{ case (k, v) => (recEval(k), recEval(v)) }, kT, vT)

    case g @ MapApply(m,k) => (recEval(m), recEval(k)) match {
      case (FiniteMap(ss, _, _), e) =>
        ss.getOrElse(e, throw RuntimeError("Key not found: " + e.asString))
      case (l,r) =>
        throw EvalError(typeErrorMsg(l, MapType(r.getType, g.getType)))
    }

    case u @ MapUnion(m1,m2) => (recEval(m1), recEval(m2)) match {
      case (f1@FiniteMap(ss1, _, _), FiniteMap(ss2, _, _)) =>
        val newSs = ss1 ++ ss2
        val MapType(kT, vT) = u.getType
        FiniteMap(newSs, kT, vT)
      case (l, r) =>
        throw EvalError(typeErrorMsg(l, m1.getType))
    }

    case i @ MapIsDefinedAt(m,k) => (recEval(m), recEval(k)) match {
      case (FiniteMap(ss, _, _), e) => BooleanLiteral(ss.contains(e))
      case (l, r) => throw EvalError(typeErrorMsg(l, m.getType))
    }
    case gl: GenericValue => gl
    case fl : FractionalLiteral => normalizeFraction(fl)
    case l : Literal[_] => l

    case other =>
      throw EvalError("Unhandled case in Evaluator : [" + other.getClass + "] " + other.asString)
  }
}

