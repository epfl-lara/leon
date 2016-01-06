/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import leon.purescala.Quantification._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Expressions.Pattern
import purescala.Extractors._
import purescala.TypeOps._
import purescala.Types._
import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import leon.solvers.{HenkinModel, Model, SolverFactory}

import scala.collection.mutable.{Map => MutableMap}

abstract class RecursiveEvaluator(ctx: LeonContext, prog: Program, maxSteps: Int)
  extends ContextualEvaluator(ctx, prog, maxSteps)
  with DeterministicEvaluator {

  val name = "evaluator"
  val description = "Recursive interpreter for PureScala expressions"

  lazy val scalaEv = new ScalacEvaluator(this, ctx, prog)

  protected var clpCache = Map[(Choose, Seq[Expr]), Expr]()

  protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case Variable(id) =>
      rctx.mappings.get(id) match {
        case Some(v) if v != expr =>
          e(v)
        case Some(v) =>
          v
        case None =>
          ctx.reporter.fatalError("No value for identifier " + id.asString + " in mapping.")
          //throw EvalError()
      }

    case Application(caller, args) =>
      e(caller) match {
        case l @ Lambda(params, body) =>
          val newArgs = args.map(e)
          val mapping = l.paramSubst(newArgs)
          e(body)(rctx.withNewVars(mapping), gctx)
        case PartialLambda(mapping, dflt, _) =>
          mapping.find { case (pargs, res) =>
            (args zip pargs).forall(p => e(Equals(p._1, p._2)) == BooleanLiteral(true))
          }.map(_._2).orElse(dflt).getOrElse {
            throw EvalError("Cannot apply partial lambda outside of domain : " +
              args.map(e(_).asString(ctx)).mkString("(", ", ", ")"))
          }
        case f =>
          throw EvalError("Cannot apply non-lambda function " + f.asString)
      }

    case Tuple(ts) =>
      val tsRec = ts.map(e)
      Tuple(tsRec)

    case TupleSelect(t, i) =>
      val Tuple(rs) = e(t)
      rs(i-1)

    case Let(i,ex,b) =>
      val first = e(ex)
      e(b)(rctx.withNewVar(i, first), gctx)

    case Assert(cond, oerr, body) =>
      e(IfExpr(Not(cond), Error(expr.getType, oerr.getOrElse("Assertion failed @"+expr.getPos)), body))

    case en@Ensuring(body, post) =>
      if ( exists{
        case Hole(_,_) => true
        case WithOracle(_,_) => true
        case _ => false
      }(en)) {
        import synthesis.ConversionPhase.convert
        e(convert(en, ctx))
      } else {
        e(en.toAssert)
      }

    case Error(tpe, desc) =>
      throw RuntimeError("Error reached in evaluation: " + desc)

    case IfExpr(cond, thenn, elze) =>
      val first = e(cond)
      first match {
        case BooleanLiteral(true) => e(thenn)
        case BooleanLiteral(false) => e(elze)
        case _ => throw EvalError(typeErrorMsg(first, BooleanType))
      }

    case FunctionInvocation(TypedFunDef(fd, Seq(tp)), Seq(set)) if fd == program.library.setToList.get =>
      val els = e(set) match {
        case FiniteSet(els, _) => els
        case _ => throw EvalError(typeErrorMsg(set, SetType(tp)))
      }
      val cons = program.library.Cons.get
      val nil = CaseClass(CaseClassType(program.library.Nil.get, Seq(tp)), Seq())
      def mkCons(h: Expr, t: Expr) = CaseClass(CaseClassType(cons, Seq(tp)), Seq(h,t))
      els.foldRight(nil)(mkCons)

    case FunctionInvocation(tfd, args) =>
      if (gctx.stepsLeft < 0) {
        throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
      }
      gctx.stepsLeft -= 1

      val evArgs = args map e

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
          throw EvalError("Evaluation of function with unknown implementation.")
        }

        val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
        e(body)(frame, gctx)
      }

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

    case And(args) if args.isEmpty => BooleanLiteral(true)
    case And(args) =>
      e(args.head) match {
        case BooleanLiteral(false) => BooleanLiteral(false)
        case BooleanLiteral(true) => e(andJoin(args.tail))
        case other => throw EvalError(typeErrorMsg(other, BooleanType))
      }

    case Or(args) if args.isEmpty => BooleanLiteral(false)
    case Or(args) =>
      e(args.head) match {
        case BooleanLiteral(true) => BooleanLiteral(true)
        case BooleanLiteral(false) => e(orJoin(args.tail))
        case other => throw EvalError(typeErrorMsg(other, BooleanType))
      }

    case Not(arg) =>
      e(arg) match {
        case BooleanLiteral(v) => BooleanLiteral(!v)
        case other => throw EvalError(typeErrorMsg(other, BooleanType))
      }

    case Implies(l,r) =>
      e(l) match {
        case BooleanLiteral(false) => BooleanLiteral(true)
        case BooleanLiteral(true) => e(r)
        case le => throw EvalError(typeErrorMsg(le, BooleanType))
      }

    case Equals(le,re) =>
      val lv = e(le)
      val rv = e(re)

      (lv,rv) match {
        case (FiniteSet(el1, _),FiniteSet(el2, _)) => BooleanLiteral(el1 == el2)
        case (FiniteMap(el1, _, _),FiniteMap(el2, _, _)) => BooleanLiteral(el1.toSet == el2.toSet)
        case (PartialLambda(m1, d1, _), PartialLambda(m2, d2, _)) => BooleanLiteral(m1.toSet == m2.toSet && d1 == d2)
        case _ => BooleanLiteral(lv == rv)
      }

    case CaseClass(cd, args) =>
      CaseClass(cd, args.map(e))

    case AsInstanceOf(expr, ct) =>
      val le = e(expr)
      if (isSubtypeOf(le.getType, ct)) {
        le
      } else {
        throw RuntimeError("Cast error: cannot cast "+le.asString+" to "+ct.asString)
      }

    case IsInstanceOf(expr, ct) =>
      val le = e(expr)
      BooleanLiteral(isSubtypeOf(le.getType, ct))

    case CaseClassSelector(ct1, expr, sel) =>
      val le = e(expr)
      le match {
        case CaseClass(ct2, args) if ct1 == ct2 => args(ct1.classDef.selectorID2Index(sel))
        case _ => throw EvalError(typeErrorMsg(le, ct1))
      }

    case Plus(l,r) =>
      (e(l), e(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 + i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }

    case Minus(l,r) =>
      (e(l), e(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 - i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }

    case RealPlus(l, r) =>
      (e(l), e(r)) match {
        case (FractionalLiteral(ln, ld), FractionalLiteral(rn, rd)) =>
          normalizeFraction(FractionalLiteral(ln * rd + rn * ld, ld * rd))
        case (le, re) => throw EvalError(typeErrorMsg(le, RealType))
      }

    case RealMinus(l,r) =>
      e(RealPlus(l, RealUMinus(r)))
      
    case StringConcat(l, r) =>
      (e(l), e(r)) match {
        case (StringLiteral(i1), StringLiteral(i2)) => StringLiteral(i1 + i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, StringType))
      }
    case StringLength(a) => e(a) match {
      case StringLiteral(a) => InfiniteIntegerLiteral(a.length)
      case res => throw EvalError(typeErrorMsg(res, IntegerType))
    }
    case SubString(a, start, end) => (e(a), e(start), e(end)) match {
      case (StringLiteral(a), InfiniteIntegerLiteral(b), InfiniteIntegerLiteral(c))  =>
        StringLiteral(a.substring(b.toInt, c.toInt))
      case res => throw EvalError(typeErrorMsg(res._1, StringType))
    }
    case Int32ToString(a) => e(a) match {
      case IntLiteral(i) => StringLiteral(i.toString)
      case res =>  throw EvalError(typeErrorMsg(res, Int32Type))
    }
    case CharToString(a) => 
      e(a) match {
        case CharLiteral(i) => StringLiteral(i.toString)
        case res =>  throw EvalError(typeErrorMsg(res, CharType))
      }
    case IntegerToString(a) => e(a) match {
        case InfiniteIntegerLiteral(i) => StringLiteral(i.toString)
        case res =>  throw EvalError(typeErrorMsg(res, IntegerType))
      }
    case BooleanToString(a) => e(a) match {
        case BooleanLiteral(i) => StringLiteral(i.toString)
        case res =>  throw EvalError(typeErrorMsg(res, BooleanType))
      }
    case RealToString(a) => e(a) match {
        case FractionalLiteral(n, d) => StringLiteral(n.toString + "/" + d.toString)
        case res =>  throw EvalError(typeErrorMsg(res, RealType))
      }
    case StringEscape(a) => e(a) match {
      case StringLiteral(i) => StringLiteral(codegen.runtime.StrOps.escape(i))
      case res => throw EvalError(typeErrorMsg(res, StringType))
    }
    
    case BVPlus(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVMinus(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case UMinus(ex) =>
      e(ex) match {
        case InfiniteIntegerLiteral(i) => InfiniteIntegerLiteral(-i)
        case re => throw EvalError(typeErrorMsg(re, IntegerType))
      }

    case BVUMinus(ex) =>
      e(ex) match {
        case IntLiteral(i) => IntLiteral(-i)
        case re => throw EvalError(typeErrorMsg(re, Int32Type))
      }

    case RealUMinus(ex) =>
      e(ex) match {
        case FractionalLiteral(n, d) => FractionalLiteral(-n, d)
        case re => throw EvalError(typeErrorMsg(re, RealType))
      }


    case BVNot(ex) =>
      e(ex) match {
        case IntLiteral(i) => IntLiteral(~i)
        case re => throw EvalError(typeErrorMsg(re, Int32Type))
      }

    case Times(l,r) =>
      (e(l), e(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 * i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }

    case Division(l,r) =>
      (e(l), e(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) =>
          if(i2 != BigInt(0)) InfiniteIntegerLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }

    case Remainder(l,r) =>
      (e(l), e(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) =>
          if(i2 != BigInt(0)) InfiniteIntegerLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, IntegerType))
      }
    case Modulo(l,r) =>
      (e(l), e(r)) match {
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
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVDivision(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) =>
          if(i2 != 0) IntLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVRemainder(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) =>
          if(i2 != 0) IntLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case RealTimes(l,r) =>
      (e(l), e(r)) match {
        case (FractionalLiteral(ln, ld), FractionalLiteral(rn, rd)) =>
          normalizeFraction(FractionalLiteral((ln * rn), (ld * rd)))
        case (le,re) => throw EvalError(typeErrorMsg(le, RealType))
      }

    case RealDivision(l,r) =>
      (e(l), e(r)) match {
        case (FractionalLiteral(ln, ld), FractionalLiteral(rn, rd)) =>
          if (rn != 0)
            normalizeFraction(FractionalLiteral(ln * rd, ld * rn))
          else throw RuntimeError("Division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, RealType))
      }


    case BVAnd(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 & i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVOr(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 | i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVXOr(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 ^ i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVShiftLeft(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 << i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVAShiftRight(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 >> i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case BVLShiftRight(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 >>> i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case LessThan(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 < i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 < i2)
        case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = e(RealMinus(a, b))
          BooleanLiteral(n < 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 < c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case GreaterThan(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = e(RealMinus(a, b))
          BooleanLiteral(n > 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 > c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case LessEquals(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = e(RealMinus(a, b))
          BooleanLiteral(n <= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 <= c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case GreaterEquals(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = e(RealMinus(a, b))
          BooleanLiteral(n >= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 >= c2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case SetUnion(s1,s2) =>
      (e(s1), e(s2)) match {
        case (f@FiniteSet(els1, _),FiniteSet(els2, _)) =>
          val SetType(tpe) = f.getType
          FiniteSet(els1 ++ els2, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetIntersection(s1,s2) =>
      (e(s1), e(s2)) match {
        case (f @ FiniteSet(els1, _), FiniteSet(els2, _)) =>
          val newElems = els1 intersect els2
          val SetType(tpe) = f.getType
          FiniteSet(newElems, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetDifference(s1,s2) =>
      (e(s1), e(s2)) match {
        case (f @ FiniteSet(els1, _),FiniteSet(els2, _)) =>
          val SetType(tpe) = f.getType
          val newElems = els1 -- els2
          FiniteSet(newElems, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case ElementOfSet(el,s) => (e(el), e(s)) match {
      case (e, f @ FiniteSet(els, _)) => BooleanLiteral(els.contains(e))
      case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
    }
    case SubsetOf(s1,s2) => (e(s1), e(s2)) match {
      case (f@FiniteSet(els1, _),FiniteSet(els2, _)) => BooleanLiteral(els1.subsetOf(els2))
      case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
    }
    case SetCardinality(s) =>
      val sr = e(s)
      sr match {
        case FiniteSet(els, _) => InfiniteIntegerLiteral(els.size)
        case _ => throw EvalError(typeErrorMsg(sr, SetType(Untyped)))
      }

    case f @ FiniteSet(els, base) =>
      FiniteSet(els.map(e), base)

    case l @ Lambda(_, _) =>
      val (nl, structSubst) = normalizeStructure(matchToIfThenElse(l))
      val mapping = variablesOf(l).map(id => structSubst(id) -> e(Variable(id))).toMap
      val newLambda = replaceFromIDs(mapping, nl).asInstanceOf[Lambda]
      if (!gctx.lambdas.isDefinedAt(newLambda)) {
        gctx.lambdas += (newLambda -> nl.asInstanceOf[Lambda])
      }
      newLambda

    case PartialLambda(mapping, dflt, tpe) =>
      PartialLambda(mapping.map(p => p._1.map(e) -> e(p._2)), dflt.map(e), tpe)

    case Forall(fargs, body) =>
      evalForall(fargs.map(_.id).toSet, body)

    case ArrayLength(a) =>
      val FiniteArray(_, _, IntLiteral(length)) = e(a)
      IntLiteral(length)

    case ArrayUpdated(a, i, v) =>
      val ra = e(a)
      val ri = e(i)
      val rv = e(v)

      val IntLiteral(index) = ri
      val FiniteArray(elems, default, length) = ra
      val ArrayType(tp) = ra.getType
      finiteArray(elems.updated(index, rv), default map { (_, length) }, tp)

    case ArraySelect(a, i) =>
      val IntLiteral(index) = e(i)
      val FiniteArray(elems, default, _) = e(a)
      try {
        elems.get(index).orElse(default).get
      } catch {
        case e : IndexOutOfBoundsException => throw RuntimeError(e.getMessage)
      }

    case f @ FiniteArray(elems, default, length) =>
      val ArrayType(tp) = f.getType
      finiteArray(
        elems.map(el => (el._1, e(el._2))),
        default.map{ d => (e(d), e(length)) },
        tp
      )

    case f @ FiniteMap(ss, kT, vT) =>
      FiniteMap(ss.map{ case (k, v) => (e(k), e(v)) }, kT, vT)

    case g @ MapApply(m,k) => (e(m), e(k)) match {
      case (FiniteMap(ss, _, _), e) =>
        ss.getOrElse(e, throw RuntimeError("Key not found: " + e.asString))
      case (l,r) =>
        throw EvalError(typeErrorMsg(l, MapType(r.getType, g.getType)))
    }
    case u @ MapUnion(m1,m2) => (e(m1), e(m2)) match {
      case (f1@FiniteMap(ss1, _, _), FiniteMap(ss2, _, _)) =>
        val newSs = ss1 ++ ss2
        val MapType(kT, vT) = u.getType
        FiniteMap(newSs, kT, vT)
      case (l, r) =>
        throw EvalError(typeErrorMsg(l, m1.getType))
    }
    case i @ MapIsDefinedAt(m,k) => (e(m), e(k)) match {
      case (FiniteMap(ss, _, _), e) => BooleanLiteral(ss.contains(e))
      case (l, r) => throw EvalError(typeErrorMsg(l, m.getType))
    }

    case p : Passes =>
      e(p.asConstraint)

    case choose: Choose =>

      implicit val debugSection = utils.DebugSectionSynthesis

      val p = synthesis.Problem.fromSpec(choose.pred)

      ctx.reporter.debug("Executing choose!")

      val ins = p.as.map(rctx.mappings(_))

      clpCache.getOrElse((choose, ins), {
        val tStart = System.currentTimeMillis

        val solverf = SolverFactory.getFromSettings(ctx, program)
        val solver  = solverf.getNewSolver()


        try {
          val eqs = p.as.map {
            case id =>
              Equals(Variable(id), rctx.mappings(id))
          }

          val cnstr = andJoin(eqs ::: p.pc :: p.phi :: Nil)
          solver.assertCnstr(cnstr)

          solver.check match {
            case Some(true) =>
              val model = solver.getModel

              val valModel = valuateWithModel(model) _

              val res = p.xs.map(valModel)
              val leonRes = tupleWrap(res)
              val total = System.currentTimeMillis-tStart

              ctx.reporter.debug("Synthesis took "+total+"ms")
              ctx.reporter.debug("Finished synthesis with "+leonRes.asString)

              clpCache += (choose, ins) -> leonRes
              leonRes
            case Some(false) =>
              throw RuntimeError("Constraint is UNSAT")
            case _ =>
              throw RuntimeError("Timeout exceeded")
          }
        } catch {
          case e: Throwable =>
            throw EvalError("Runtime synthesis of choose failed: "+e.getMessage)
        } finally {
          solverf.reclaim(solver)
          solverf.shutdown()
        }
      })

    case MatchExpr(scrut, cases) =>
      val rscrut = e(scrut)
      cases.toStream.map(c => matchesCase(rscrut, c)).find(_.nonEmpty) match {
        case Some(Some((c, mappings))) =>
          e(c.rhs)(rctx.withNewVars(mappings), gctx)
        case _ =>
          throw RuntimeError("MatchError: "+rscrut.asString+" did not match any of the cases")
      }

    case gl: GenericValue => gl
    case fl : FractionalLiteral => normalizeFraction(fl)
    case l : Literal[_] => l

    case other =>
      context.reporter.error(other.getPos, "Error: don't know how to handle " + other.asString + " in Evaluator ("+other.getClass+").")
      throw EvalError("Unhandled case in Evaluator : " + other.asString)
  }

  def matchesCase(scrut: Expr, caze: MatchCase)(implicit rctx: RC, gctx: GC): Option[(MatchCase, Map[Identifier, Expr])] = {
    import purescala.TypeOps.isSubtypeOf

    def matchesPattern(pat: Pattern, expr: Expr): Option[Map[Identifier, Expr]] = (pat, expr) match {
      case (InstanceOfPattern(ob, pct), e) =>
        if (isSubtypeOf(e.getType, pct)) {
          Some(obind(ob, e))
        } else {
          None
        }
      case (WildcardPattern(ob), e) =>
        Some(obind(ob, e))

      case (CaseClassPattern(ob, pct, subs), CaseClass(ct, args)) =>
        if (pct == ct) {
          val res = (subs zip args).map{ case (s, a) => matchesPattern(s, a) }
          if (res.forall(_.isDefined)) {
            Some(obind(ob, expr) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }
      case (up @ UnapplyPattern(ob, _, subs), scrut) =>
        e(functionInvocation(up.unapplyFun.fd, Seq(scrut))) match {
          case CaseClass(CaseClassType(cd, _), Seq()) if cd == program.library.None.get =>
            None
          case CaseClass(CaseClassType(cd, _), Seq(arg)) if cd == program.library.Some.get =>
            val res = subs zip unwrapTuple(arg, subs.size) map {
              case (s,a) => matchesPattern(s,a)
            }
            if (res.forall(_.isDefined)) {
              Some(obind(ob, expr) ++ res.flatten.flatten)
            } else {
              None
            }
          case other =>
            throw EvalError(typeErrorMsg(other, up.unapplyFun.returnType))
        }
      case (TuplePattern(ob, subs), Tuple(args)) =>
        if (subs.size == args.size) {
          val res = (subs zip args).map{ case (s, a) => matchesPattern(s, a) }
          if (res.forall(_.isDefined)) {
            Some(obind(ob, expr) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }
      case (LiteralPattern(ob, l1) , l2 : Literal[_]) if l1 == l2 =>
        Some(obind(ob,l1))
      case _ => None
    }

    def obind(ob: Option[Identifier], e: Expr): Map[Identifier, Expr] = {
      Map[Identifier, Expr]() ++ ob.map(id => id -> e)
    }

    caze match {
      case SimpleCase(p, rhs) =>
        matchesPattern(p, scrut).map(r =>
          (caze, r)
        )

      case GuardedCase(p, g, rhs) =>
        for {
          r <- matchesPattern(p, scrut)
          if e(g)(rctx.withNewVars(r), gctx) == BooleanLiteral(true)
        } yield (caze, r)
    }
  }


  protected def evalForall(quants: Set[Identifier], body: Expr, check: Boolean = true)(implicit rctx: RC, gctx: GC): Expr = {
    val henkinModel: HenkinModel = gctx.model match {
      case hm: HenkinModel => hm
      case _ => throw EvalError("Can't evaluate foralls without henkin model")
}

    val TopLevelAnds(conjuncts) = body
    e(andJoin(conjuncts.flatMap { conj =>
      val vars = variablesOf(conj)
      val quantified = quants.filter(vars)

      extractQuorums(conj, quantified).flatMap { case (qrm, others) =>
        val quorum = qrm.toList

        if (quorum.exists { case (TopLevelAnds(paths), _, _) =>
          val p = andJoin(paths.filter(path => (variablesOf(path) & quantified).isEmpty))
          e(p) == BooleanLiteral(false)
        }) List(BooleanLiteral(true)) else {

          var mappings: Seq[(Identifier, Int, Int)] = Seq.empty
          var constraints: Seq[(Expr, Int, Int)] = Seq.empty
          var equalities: Seq[((Int, Int), (Int, Int))] = Seq.empty

          for (((_, expr, args), qidx) <- quorum.zipWithIndex) {
            val (qmappings, qconstraints) = args.zipWithIndex.partition {
              case (Variable(id),aidx) => quantified(id)
              case _ => false
            }

            mappings ++= qmappings.map(p => (p._1.asInstanceOf[Variable].id, qidx, p._2))
            constraints ++= qconstraints.map(p => (p._1, qidx, p._2))
          }

          val mapping = for ((id, es) <- mappings.groupBy(_._1)) yield {
            val base :: others = es.toList.map(p => (p._2, p._3))
            equalities ++= others.map(p => base -> p)
            (id -> base)
          }

          def domain(expr: Expr): Set[Seq[Expr]] = henkinModel.domain(e(expr) match {
            case l: Lambda => gctx.lambdas.getOrElse(l, l)
            case ev => ev
          })

          val argSets = quorum.foldLeft[List[Seq[Seq[Expr]]]](List(Seq.empty)) {
            case (acc, (_, expr, _)) => acc.flatMap(s => domain(expr).map(d => s :+ d))
          }

          argSets.map { args =>
            val argMap: Map[(Int, Int), Expr] = args.zipWithIndex.flatMap {
              case (a, qidx) => a.zipWithIndex.map { case (e, aidx) => (qidx, aidx) -> e }
            }.toMap

            val map = mapping.map { case (id, key) => id -> argMap(key) }
            val enabler = andJoin(constraints.map {
              case (e, qidx, aidx) => Equals(e, argMap(qidx -> aidx))
            } ++ equalities.map {
              case (k1, k2) => Equals(argMap(k1), argMap(k2))
            })

            val ctx = rctx.withNewVars(map)
            if (e(enabler)(ctx, gctx) == BooleanLiteral(true)) {
              if (gctx.check) {
                for ((b,caller,args) <- others if e(b)(ctx, gctx) == BooleanLiteral(true)) {
                  val evArgs = args.map(arg => e(arg)(ctx, gctx))
                  if (!domain(caller)(evArgs))
                    throw QuantificationError("Unhandled transitive implication in " + replaceFromIDs(map, conj))
                }
              }

              e(conj)(ctx, gctx)
            } else {
              BooleanLiteral(true)
            }
          }
        }
      }
    })) match {
      case res @ BooleanLiteral(true) if check =>
        if (gctx.check) {
          checkForall(quants, body) match {
            case status: ForallInvalid =>
              throw QuantificationError("Invalid forall: " + status.getMessage)
            case _ =>
              // make sure the body doesn't contain matches or lets as these introduce new locals
              val cleanBody = expandLets(matchToIfThenElse(body))
              val calls = new CollectorWithPaths[(Expr, Seq[Expr], Seq[Expr])] {
                def collect(e: Expr, path: Seq[Expr]): Option[(Expr, Seq[Expr], Seq[Expr])] = e match {
                  case QuantificationMatcher(IsTyped(caller, _: FunctionType), args) => Some((caller, args, path))
                  case _ => None
                }

                override def rec(e: Expr, path: Seq[Expr]): Expr = e match {
                  case l : Lambda => l
                  case _ => super.rec(e, path)
                }
              }.traverse(cleanBody)

              for ((caller, appArgs, paths) <- calls) {
                val path = andJoin(paths.filter(expr => (variablesOf(expr) & quants).isEmpty))
                if (e(path) == BooleanLiteral(true)) e(caller) match {
                  case _: PartialLambda => // OK
                  case l: Lambda =>
                    val nl @ Lambda(args, body) = gctx.lambdas.getOrElse(l, l)
                    val lambdaQuantified = (appArgs zip args).collect {
                      case (Variable(id), vd) if quants(id) => vd.id
                    }.toSet

                    if (lambdaQuantified.nonEmpty) {
                      checkForall(lambdaQuantified, body) match {
                        case lambdaStatus: ForallInvalid =>
                          throw QuantificationError("Invalid forall: " + lambdaStatus.getMessage)
                        case _ => // do nothing
                      }

                      val axiom = Equals(Application(nl, args.map(_.toVariable)), nl.body)
                      if (evalForall(args.map(_.id).toSet, axiom, check = false) == BooleanLiteral(false)) {
                        throw QuantificationError("Unaxiomatic lambda " + l)
                      }
                    }
                  case f =>
                    throw EvalError("Cannot apply non-lambda function " + f.asString)
                }
              }
          }
        }

        res

      // `res == false` means the quantification is valid since there effectivelly must
      // exist an input for which the proposition doesn't hold
      case res => res
    }
  }

}

