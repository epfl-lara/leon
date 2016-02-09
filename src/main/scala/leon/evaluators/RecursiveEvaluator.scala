/* Copyright 2009-2015 EPFL, Lausanne */

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
import purescala.DefOps
import solvers.{HenkinModel, Model, SolverFactory}
import solvers.combinators.UnrollingProcedure
import scala.collection.mutable.{Map => MutableMap}
import scala.concurrent.duration._
import org.apache.commons.lang3.StringEscapeUtils

abstract class RecursiveEvaluator(ctx: LeonContext, prog: Program, maxSteps: Int)
  extends ContextualEvaluator(ctx, prog, maxSteps)
  with DeterministicEvaluator {

  val name = "evaluator"
  val description = "Recursive interpreter for PureScala expressions"

  lazy val scalaEv = new ScalacEvaluator(this, ctx, prog)

  protected var clpCache = Map[(Choose, Seq[Expr]), Expr]()
  protected var frlCache = Map[(Forall, Seq[Expr]), Expr]()

  private var evaluationFailsOnChoose = false
  /** Sets the flag if when encountering a Choose, it should fail instead of solving it. */
  def setEvaluationFailOnChoose(b: Boolean) = { this.evaluationFailsOnChoose = b; this }

  protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case Variable(id) =>
      rctx.mappings.get(id) match {
        case Some(v) if v != expr =>
          e(v)
        case Some(v) =>
          v
        case None =>
          throw EvalError("No value for identifier " + id.asString + " in mapping " + rctx.mappings)
      }

    case Application(caller, args) =>
      e(caller) match {
        case l @ Lambda(params, body) =>
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
      e(en.toAssert)

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

    case FunctionInvocation(TypedFunDef(fd, Nil), Seq(input)) if fd == program.library.escape.get =>
       e(input) match {
         case StringLiteral(s) => 
           StringLiteral(StringEscapeUtils.escapeJava(s))
         case _ => throw EvalError(typeErrorMsg(input, StringType))
       }

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
        case (FiniteLambda(m1, d1, _), FiniteLambda(m2, d2, _)) => BooleanLiteral(m1.toSet == m2.toSet && d1 == d2)
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

    case FiniteLambda(mapping, dflt, tpe) =>
      FiniteLambda(mapping.map(p => p._1.map(e) -> e(p._2)), e(dflt), tpe)

    case f @ Forall(fargs, body) =>

      implicit val debugSection = utils.DebugSectionVerification

      ctx.reporter.debug("Executing forall!")

      val mapping = variablesOf(f).map(id => id -> rctx.mappings(id)).toMap
      val context = mapping.toSeq.sortBy(_._1.uniqueName).map(_._2)

      frlCache.getOrElse((f, context), {
        val tStart = System.currentTimeMillis

        val newCtx = ctx.copy(options = ctx.options.map {
          case LeonOption(optDef, value) if optDef == UnrollingProcedure.optFeelingLucky =>
            LeonOption(optDef)(false)
          case opt => opt
        })

        val solverf = SolverFactory.getFromSettings(newCtx, program).withTimeout(1.second)
        val solver  = solverf.getNewSolver()

        try {
          val cnstr = Not(replaceFromIDs(mapping, body))
          solver.assertCnstr(cnstr)

          gctx.model match {
            case pm: HenkinModel =>
              val quantifiers = fargs.map(_.id).toSet
              val quorums = extractQuorums(body, quantifiers)

              val domainCnstr = orJoin(quorums.map { quorum =>
                val quantifierDomains = quorum.flatMap { case (path, caller, args) =>
                  val matcher = e(expr) match {
                    case l: Lambda => gctx.lambdas.getOrElse(l, l)
                    case ev => ev
                  }

                  val domain = pm.domain(matcher)
                  args.zipWithIndex.flatMap {
                    case (Variable(id),idx) if quantifiers(id) =>
                      Some(id -> domain.map(cargs => path -> cargs(idx)))
                    case _ => None
                  }
                }

                val domainMap = quantifierDomains.groupBy(_._1).mapValues(_.map(_._2).flatten)
                andJoin(domainMap.toSeq.map { case (id, dom) =>
                  orJoin(dom.toSeq.map { case (path, value) => and(path, Equals(Variable(id), value)) })
                })
              })

              solver.assertCnstr(domainCnstr)

            case _ =>
          }

          solver.check match {
            case Some(negRes) =>
              val total = System.currentTimeMillis-tStart
              val res = BooleanLiteral(!negRes)
              ctx.reporter.debug("Verification took "+total+"ms")
              ctx.reporter.debug("Finished forall evaluation with: "+res)

              frlCache += (f, context) -> res
              res
            case _ =>
              throw RuntimeError("Timeout exceeded")
          }
        } catch {
          case e: Throwable =>
            throw EvalError("Runtime verification of forall failed: "+e.getMessage)
        } finally {
          solverf.reclaim(solver)
          solverf.shutdown()
        }
      })

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
      if(evaluationFailsOnChoose) {
        throw EvalError("Evaluator set to not solve choose constructs")
      }

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
          throw RuntimeError("MatchError: "+rscrut.asString+" did not match any of the cases:\n"+cases)
      }

    case gl: GenericValue => gl
    case fl : FractionalLiteral => normalizeFraction(fl)
    case l : Literal[_] => l

    case other =>
      throw EvalError("Unhandled case in Evaluator : [" + other.getClass + "] " + other.asString)
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
}

