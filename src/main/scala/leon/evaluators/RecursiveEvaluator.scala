/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.ExprOps._
import purescala.Expressions._
import purescala.Types._
import purescala.Constructors._
import purescala.Extractors._

import solvers.TimeoutSolver

import xlang.Expressions._
import solvers.SolverFactory
import synthesis.ConvertHoles.convertHoles

abstract class RecursiveEvaluator(ctx: LeonContext, prog: Program, maxSteps: Int) extends Evaluator(ctx, prog) {
  val name = "evaluator"
  val description = "Recursive interpreter for PureScala expressions"

  type RC <: RecContext
  type GC <: GlobalContext

  var lastGC: Option[GC] = None

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

  class GlobalContext {
    def maxSteps = RecursiveEvaluator.this.maxSteps

    var stepsLeft = maxSteps
  }

  def initRC(mappings: Map[Identifier, Expr]): RC
  def initGC: GC

  private[this] var clpCache = Map[(Choose, Seq[Expr]), Expr]()

  def eval(ex: Expr, mappings: Map[Identifier, Expr]) = {
    try {
      lastGC = Some(initGC)
      ctx.timers.evaluators.recursive.runtime.start()
      EvaluationResults.Successful(e(ex)(initRC(mappings), lastGC.get))
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

  def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case Variable(id) =>
      rctx.mappings.get(id) match {
        case Some(v) if v != expr =>
          e(v)
        case Some(v) =>
          v
        case None =>
          throw EvalError("No value for identifier " + id.name + " in mapping.")
      }

    case Application(caller, args) =>
      e(caller) match {
        case Lambda(params, body) =>
          val newArgs = args.map(e)
          val mapping = (params.map(_.id) zip newArgs).toMap
          e(body)(rctx.withNewVars(mapping), gctx)
        case f =>
          throw EvalError("Cannot apply non-lambda function " + f)
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
        case Gives(_,_) => true
        case _ => false
      }(en)) 
        e(convertHoles(en, ctx, true))
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
        case FiniteSet(els) => els
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

      val evArgs = args.map(a => e(a))

      // build a mapping for the function...
      val frame = rctx.newVars((tfd.params.map(_.id) zip evArgs).toMap)
      
      if(tfd.hasPrecondition) {
        e(tfd.precondition.get)(frame, gctx) match {
          case BooleanLiteral(true) =>
          case BooleanLiteral(false) =>
            throw RuntimeError("Precondition violation for " + tfd.id.name + " reached in evaluation.: " + tfd.precondition.get)
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
            case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + tfd.id.name + " reached in evaluation.")
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
        case (FiniteSet(el1),FiniteSet(el2)) => BooleanLiteral(el1.toSet == el2.toSet)
        case (FiniteMap(el1),FiniteMap(el2)) => BooleanLiteral(el1.toSet == el2.toSet)
        case (BooleanLiteral(b1),BooleanLiteral(b2)) => BooleanLiteral(b1 == b2)
        case _ => BooleanLiteral(lv == rv)
      }

    case CaseClass(cd, args) =>
      CaseClass(cd, args.map(e))

    case CaseClassInstanceOf(cct, expr) =>
      val le = e(expr)
      BooleanLiteral(le.getType match {
        case CaseClassType(cd2, _) if cd2 == cct.classDef => true
        case _ => false
      })

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

    case Modulo(l,r) =>
      (e(l), e(r)) match {
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => 
          if(i2 != BigInt(0)) InfiniteIntegerLiteral(i1 % i2) else throw RuntimeError("Modulo by 0.")
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

    case BVModulo(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => 
          if(i2 != 0) IntLiteral(i1 % i2) else throw RuntimeError("Modulo by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
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
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case GreaterThan(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case LessEquals(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case GreaterEquals(l,r) =>
      (e(l), e(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case SetUnion(s1,s2) =>
      (e(s1), e(s2)) match {
        case (f@FiniteSet(els1),FiniteSet(els2)) => 
          val SetType(tpe) = f.getType
          finiteSet(els1 ++ els2, tpe)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetIntersection(s1,s2) =>
      (e(s1), e(s2)) match {
        case (f @ FiniteSet(els1), FiniteSet(els2)) => {
          val newElems = els1 intersect els2
          val SetType(tpe) = f.getType
          finiteSet(newElems, tpe)
        }
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetDifference(s1,s2) =>
      (e(s1), e(s2)) match {
        case (f @ FiniteSet(els1),FiniteSet(els2)) => {
          val SetType(tpe) = f.getType
          val newElems = els1 -- els2
          finiteSet(newElems, tpe)
        }
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case ElementOfSet(el,s) => (e(el), e(s)) match {
      case (e, f @ FiniteSet(els)) => BooleanLiteral(els.contains(e))
      case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
    }
    case SubsetOf(s1,s2) => (e(s1), e(s2)) match {
      case (f@FiniteSet(els1),FiniteSet(els2)) => BooleanLiteral(els1.toSet.subsetOf(els2.toSet))
      case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
    }
    case SetCardinality(s) =>
      val sr = e(s)
      sr match {
        case FiniteSet(els) => IntLiteral(els.size)
        case _ => throw EvalError(typeErrorMsg(sr, SetType(Untyped)))
      }

    case f @ FiniteSet(els) => 
      val SetType(tp) = f.getType
      finiteSet(els.map(e), tp)
    case i @ IntLiteral(_) => i
    case i @ InfiniteIntegerLiteral(_) => i
    case b @ BooleanLiteral(_) => b
    case u @ UnitLiteral() => u
    case l @ Lambda(_, _) =>
      val mapping = variablesOf(l).map(id => id -> e(Variable(id))).toMap
      replaceFromIDs(mapping, l)

    case ArrayLength(a) =>
      var FiniteArray(elems, default, IntLiteral(length)) = e(a)
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
      val FiniteArray(elems, default, length) = e(a)
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

    case f @ FiniteMap(ss) => 
      val MapType(kT, vT) = f.getType
      finiteMap(ss.map{ case (k, v) => (e(k), e(v)) }.distinct, kT, vT)
    case g @ MapGet(m,k) => (e(m), e(k)) match {
      case (FiniteMap(ss), e) => ss.find(_._1 == e) match {
        case Some((_, v0)) => v0
        case None => throw RuntimeError("Key not found: " + e)
      }
      case (l,r) => throw EvalError(typeErrorMsg(l, MapType(r.getType, g.getType)))
    }
    case u @ MapUnion(m1,m2) => (e(m1), e(m2)) match {
      case (f1@FiniteMap(ss1), FiniteMap(ss2)) => {
        val filtered1 = ss1.filterNot(s1 => ss2.exists(s2 => s2._1 == s1._1))
        val newSs = filtered1 ++ ss2
        val MapType(kT, vT) = u.getType
        finiteMap(newSs, kT, vT)
      }
      case (l, r) => throw EvalError(typeErrorMsg(l, m1.getType))
    }
    case i @ MapIsDefinedAt(m,k) => (e(m), e(k)) match {
      case (FiniteMap(ss), e) => BooleanLiteral(ss.exists(_._1 == e))
      case (l, r) => throw EvalError(typeErrorMsg(l, m.getType))
    }

    case gv: GenericValue =>
      gv

    case g : Gives =>
      e(convertHoles(g, ctx, true)) 
  
    case p : Passes => 
      e(p.asConstraint)

    case choose @ Choose(_, Some(impl)) =>
      e(impl)

    case choose @ Choose(_, None) =>
      import purescala.ExprOps.simplestValue

      implicit val debugSection = utils.DebugSectionSynthesis

      val p = synthesis.Problem.fromChoose(choose)

      ctx.reporter.debug("Executing choose!")

      val ins = p.as.map(rctx.mappings(_))

      if (clpCache contains (choose, ins)) {
        clpCache((choose, ins))
      } else {
        val tStart = System.currentTimeMillis

        val solver = SolverFactory.getFromSettings(ctx, program).getNewSolver()

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
              ctx.reporter.debug("Finished synthesis with "+leonRes.asString(ctx))

              clpCache += (choose, ins) -> leonRes
              leonRes
            case Some(false) =>
              throw RuntimeError("Constraint is UNSAT")
            case _ =>
              throw RuntimeError("Timeout exceeded")
          }
        } finally {
          solver.free()
        }
      }

    case MatchExpr(scrut, cases) =>
      val rscrut = e(scrut)

      cases.toStream.map(c => matchesCase(rscrut, c)).find(_.nonEmpty) match {
        case Some(Some((c, mappings))) =>
          e(c.rhs)(rctx.withNewVars(mappings), gctx)
        case _ =>
          throw RuntimeError("MatchError: "+rscrut+" did not match any of the cases")
      }

    case other =>
      context.reporter.error(other.getPos, "Error: don't know how to handle " + other + " in Evaluator.")
      throw EvalError("Unhandled case in Evaluator : " + other) 
  }

  def matchesCase(scrut: Expr, caze: MatchCase)(implicit rctx: RC, gctx: GC): Option[(MatchCase, Map[Identifier, Expr])] = {
    import purescala.TypeOps.isSubtypeOf

    def matchesPattern(pat: Pattern, e: Expr): Option[Map[Identifier, Expr]] = (pat, e) match {
      case (InstanceOfPattern(ob, pct), CaseClass(ct, _)) =>
        if (isSubtypeOf(ct, pct)) {
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
            Some(obind(ob, e) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }
      case (TuplePattern(ob, subs), Tuple(args)) =>
        if (subs.size == args.size) {
          val res = (subs zip args).map{ case (s, a) => matchesPattern(s, a) }
          if (res.forall(_.isDefined)) {
            Some(obind(ob, e) ++ res.flatten.flatten)
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
        matchesPattern(p, scrut).map( r =>
          (caze, r)
        )

      case GuardedCase(p, g, rhs) =>
        matchesPattern(p, scrut).flatMap( r =>
          e(g)(rctx.withNewVars(r), gctx) match {
            case BooleanLiteral(true) =>
              Some((caze, r))
            case _ =>
              None
          }
        )
    }
  }

  def typeErrorMsg(tree : Expr, expected : TypeTree) : String = s"Type error : expected $expected, found $tree."

}
