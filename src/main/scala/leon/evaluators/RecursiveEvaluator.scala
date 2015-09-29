/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.ExprOps._
import purescala.Expressions._
import purescala.Types._
import purescala.TypeOps.isSubtypeOf
import purescala.Constructors._
import purescala.Extractors._
import purescala.Quantification._
import solvers.{Model, HenkinModel}
import solvers.SolverFactory
import synthesis.ConvertHoles.convertHoles
import leon.purescala.ExprOps

abstract class RecursiveEvaluator(ctx: LeonContext, prog: Program, maxSteps: Int) extends Evaluator(ctx, prog) {
  val name = "evaluator"
  val description = "Recursive interpreter for PureScala expressions"

  private implicit val ctx0 = ctx

  type RC <: RecContext
  type GC <: GlobalContext

  case class EvalError(msg : String) extends Exception
  case class RuntimeError(msg : String) extends Exception

  trait RecContext {
    def mappings: Map[Identifier, Expr]

    def newVars(news: Map[Identifier, Expr]): RC

    def withNewVar(id: Identifier, v: Expr): RC = {
      newVars(mappings + (id -> v))
    }

    def withNewVars(news: Map[Identifier, Expr]): RC = {
      newVars(mappings ++ news)
    }
  }

  class GlobalContext(val model: Model) {
    def maxSteps = RecursiveEvaluator.this.maxSteps

    var stepsLeft = maxSteps
  }

  def initRC(mappings: Map[Identifier, Expr]): RC
  def initGC(model: Model): GC

  // Used by leon-web, please do not delete
  var lastGC: Option[GC] = None

  private[this] var clpCache = Map[(Choose, Seq[Expr]), Expr]()

  def eval(ex: Expr, model: Model) = {
    try {
      lastGC = Some(initGC(model))
      ctx.timers.evaluators.recursive.runtime.start()
      EvaluationResults.Successful(e(ex)(initRC(model.toMap), lastGC.get))
    } catch {
      case so: StackOverflowError =>
        EvaluationResults.EvaluatorError("Stack overflow")
      case EvalError(msg) =>
        EvaluationResults.EvaluatorError(msg)
      case e @ RuntimeError(msg) =>
        EvaluationResults.RuntimeError(msg)
      case jre: java.lang.RuntimeException =>
        EvaluationResults.RuntimeError(jre.getMessage)
    } finally {
      ctx.timers.evaluators.recursive.runtime.stop()
    }
  }

  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case Variable(id) =>
      rctx.mappings.get(id) match {
        case Some(v) if v != expr =>
          e(v)
        case Some(v) =>
          v
        case None =>
          throw EvalError("No value for identifier " + id.asString + " in mapping.")
      }

    case Application(caller, args) =>
      e(caller) match {
        case l @ Lambda(params, body) =>
          val newArgs = args.map(e)
          val mapping = l.paramSubst(newArgs)
          e(body)(rctx.withNewVars(mapping), gctx)
        case PartialLambda(mapping, _) =>
          mapping.find { case (pargs, res) =>
            (args zip pargs).forall(p => e(Equals(p._1, p._2)) == BooleanLiteral(true))
          }.map(_._2).getOrElse {
            throw EvalError("Cannot apply partial lambda outside of domain")
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
        case _ => false
      }(en))
        e(convertHoles(en, ctx))
      else
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

      if(!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) {
        throw EvalError("Evaluation of function with unknown implementation.")
      }

      val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
      val callResult = e(body)(frame, gctx)

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

    case And(args) if args.isEmpty =>
      BooleanLiteral(true)

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
      (e(l), e(r)) match {
        case (BooleanLiteral(b1),BooleanLiteral(b2)) => BooleanLiteral(!b1 || b2)
        case (le, re) => throw EvalError(typeErrorMsg(le, BooleanType))
      }

    case Equals(le,re) =>
      val lv = e(le)
      val rv = e(re)

      (lv,rv) match {
        case (FiniteSet(el1, _),FiniteSet(el2, _)) => BooleanLiteral(el1 == el2)
        case (FiniteMap(el1, _, _),FiniteMap(el2, _, _)) => BooleanLiteral(el1.toSet == el2.toSet)
        case (PartialLambda(m1, _), PartialLambda(m2, _)) => BooleanLiteral(m1.toSet == m2.toSet)
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
          normalizeFraction(FractionalLiteral((ln * rd + rn * ld), (ld * rd)))
        case (le, re) => throw EvalError(typeErrorMsg(le, RealType))
      }

    case RealMinus(l,r) =>
      e(RealPlus(l, RealUMinus(r)))

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
            normalizeFraction(FractionalLiteral((ln * rd), (ld * rn)))
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
        case (f @ FiniteSet(els1, _), FiniteSet(els2, _)) => {
          val newElems = els1 intersect els2
          val SetType(tpe) = f.getType
          FiniteSet(newElems, tpe)
        }
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetDifference(s1,s2) =>
      (e(s1), e(s2)) match {
        case (f @ FiniteSet(els1, _),FiniteSet(els2, _)) => {
          val SetType(tpe) = f.getType
          val newElems = els1 -- els2
          FiniteSet(newElems, tpe)
        }
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
        case FiniteSet(els, _) => IntLiteral(els.size)
        case _ => throw EvalError(typeErrorMsg(sr, SetType(Untyped)))
      }

    case f @ FiniteSet(els, base) =>
      FiniteSet(els.map(e), base)

    case l @ Lambda(_, _) =>
      val (nl, structSubst) = normalizeStructure(l)
      val mapping = variablesOf(l).map(id => structSubst(id) -> e(Variable(id))).toMap
      replaceFromIDs(mapping, nl)

    case PartialLambda(mapping, tpe) =>
      PartialLambda(mapping.map(p => p._1.map(e) -> e(p._2)), tpe)

    case f @ Forall(fargs, TopLevelAnds(conjuncts)) =>
      val henkinModel: HenkinModel = gctx.model match {
        case hm: HenkinModel => hm
        case _ => throw EvalError("Can't evaluate foralls without henkin model")
      }

      e(andJoin(for (conj <- conjuncts) yield {
        val vars = variablesOf(conj)
        val args = fargs.map(_.id).filter(vars)
        val quantified = args.toSet

        val matcherQuorums = extractQuorums(conj, quantified)

        val instantiations = matcherQuorums.flatMap { quorum =>
          var mappings: Seq[(Identifier, Int, Int)] = Seq.empty
          var constraints: Seq[(Expr, Int, Int)] = Seq.empty

          for (((expr, args), qidx) <- quorum.zipWithIndex) {
            val (qmappings, qconstraints) = args.zipWithIndex.partition {
              case (Variable(id),aidx) => quantified(id)
              case _ => false
            }

            mappings ++= qmappings.map(p => (p._1.asInstanceOf[Variable].id, qidx, p._2))
            constraints ++= qconstraints.map(p => (p._1, qidx, p._2))
          }

          var equalities: Seq[((Int, Int), (Int, Int))] = Seq.empty
          val mapping = for ((id, es) <- mappings.groupBy(_._1)) yield {
            val base :: others = es.toList.map(p => (p._2, p._3))
            equalities ++= others.map(p => base -> p)
            (id -> base)
          }

          val argSets = quorum.foldLeft[List[Seq[Seq[Expr]]]](List(Seq.empty)) {
            case (acc, (expr, _)) => acc.flatMap(s => henkinModel.domain(expr).map(d => s :+ d))
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

            (enabler, map)
          }
        }

        e(andJoin(instantiations.map { case (enabler, mapping) =>
          e(Implies(enabler, conj))(rctx.withNewVars(mapping), gctx)
        }))
      }))

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
      FiniteMap(ss.map{ case (k, v) => (e(k), e(v)) }.distinct, kT, vT)

    case g @ MapApply(m,k) => (e(m), e(k)) match {
      case (FiniteMap(ss, _, _), e) => ss.find(_._1 == e) match {
        case Some((_, v0)) => v0
        case None => throw RuntimeError("Key not found: " + e.asString)
      }
      case (l,r) => throw EvalError(typeErrorMsg(l, MapType(r.getType, g.getType)))
    }
    case u @ MapUnion(m1,m2) => (e(m1), e(m2)) match {
      case (f1@FiniteMap(ss1, _, _), FiniteMap(ss2, _, _)) => {
        val filtered1 = ss1.filterNot(s1 => ss2.exists(s2 => s2._1 == s1._1))
        val newSs = filtered1 ++ ss2
        val MapType(kT, vT) = u.getType
        FiniteMap(newSs, kT, vT)
      }
      case (l, r) => throw EvalError(typeErrorMsg(l, m1.getType))
    }
    case i @ MapIsDefinedAt(m,k) => (e(m), e(k)) match {
      case (FiniteMap(ss, _, _), e) => BooleanLiteral(ss.exists(_._1 == e))
      case (l, r) => throw EvalError(typeErrorMsg(l, m.getType))
    }

    case gv: GenericValue =>
      gv

    case p : Passes =>
      e(p.asConstraint)

    case choose: Choose =>

      implicit val debugSection = utils.DebugSectionSynthesis

      val p = synthesis.Problem.fromChoose(choose)

      ctx.reporter.debug("Executing choose!")

      val ins = p.as.map(rctx.mappings(_))

      clpCache.getOrElse((choose, ins), {
        val tStart = System.currentTimeMillis

        val solverf = SolverFactory.getFromSettings(ctx, program)
        val solver  = solverf.getNewSolver()

        val eqs = p.as.map {
          case id =>
            Equals(Variable(id), rctx.mappings(id))
        }

        val cnstr = andJoin(eqs ::: p.pc :: p.phi :: Nil)
        solver.assertCnstr(cnstr)

        try {
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
        e(FunctionInvocation(up.unapplyFun, Seq(scrut))) match {
          case CaseClass(CaseClassType(cd, _), Seq()) if cd == program.library.Nil.get =>
            None
          case CaseClass(CaseClassType(cd, _), Seq(arg)) if cd == program.library.Cons.get =>
            val res = subs zip unwrapTuple(arg, up.unapplyFun.returnType.isInstanceOf[TupleType]) map {
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

  def typeErrorMsg(tree : Expr, expected : TypeTree) : String = s"Type error : expected ${expected.asString}, found ${tree.asString}."

}
