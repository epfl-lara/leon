/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._
import purescala.TypeTrees._

import solvers.TimeoutSolver

import xlang.Trees._

abstract class RecursiveEvaluator(ctx: LeonContext, prog: Program) extends Evaluator(ctx, prog) {
  val name = "evaluator"
  val description = "Recursive interpreter for PureScala expressions"

  type RC <: RecContext
  type GC <: GlobalContext

  case class EvalError(msg : String) extends Exception
  case class RuntimeError(msg : String) extends Exception

  abstract class RecContext {
    val mappings: Map[Identifier, Expr]

    def withNewVar(id: Identifier, v: Expr): RC;

    def withVars(news: Map[Identifier, Expr]): RC;
  }

  class GlobalContext(var stepsLeft: Int)

  def initRC(mappings: Map[Identifier, Expr]): RC
  def initGC: GC

  def eval(e: Expr, mappings: Map[Identifier, Expr]) = {
    try {
      EvaluationResults.Successful(se(e)(initRC(mappings), initGC))
    } catch {
      case so: StackOverflowError =>
        EvaluationResults.EvaluatorError("Stack overflow")
      case EvalError(msg) =>
        EvaluationResults.EvaluatorError(msg)
      case RuntimeError(msg) =>
        EvaluationResults.RuntimeError(msg)
    }
  }

  def se(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    if (gctx.stepsLeft < 0) {
      throw RuntimeError("Exceeded number of allocated steps")
    } else {
      gctx.stepsLeft -= 1
      e(expr)
    }
  }

  def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case Variable(id) =>
      rctx.mappings.get(id) match {
        case Some(v) =>
          if(!isGround(v)) {
            throw EvalError("Substitution for identifier " + id.name + " is not ground.")
          } else {
            v
          }
        case None =>
          throw EvalError("No value for identifier " + id.name + " in mapping.")
      }

    case Tuple(ts) =>
      val tsRec = ts.map(se)
      Tuple(tsRec)

    case TupleSelect(t, i) =>
      val Tuple(rs) = se(t)
      rs(i-1)

    case Let(i,e,b) =>
      val first = se(e)
      se(b)(rctx.withNewVar(i, first), gctx)

    case Error(desc) =>
      throw RuntimeError("Error reached in evaluation: " + desc)

    case IfExpr(cond, thenn, elze) =>
      val first = se(cond)
      first match {
        case BooleanLiteral(true) => se(thenn)
        case BooleanLiteral(false) => se(elze)
        case _ => throw EvalError(typeErrorMsg(first, BooleanType))
      }

    case FunctionInvocation(tfd, args) =>
      val evArgs = args.map(a => se(a))

      // build a mapping for the function...
      val frame = rctx.withVars((tfd.args.map(_.id) zip evArgs).toMap)
      
      if(tfd.hasPrecondition) {
        se(matchToIfThenElse(tfd.precondition.get))(frame, gctx) match {
          case BooleanLiteral(true) =>
          case BooleanLiteral(false) =>
            throw RuntimeError("Precondition violation for " + tfd.id.name + " reached in evaluation.: " + tfd.precondition.get)
          case other => throw RuntimeError(typeErrorMsg(other, BooleanType))
        }
      }

      if(!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) {
        throw EvalError("Evaluation of function with unknown implementation.")
      }

      val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
      val callResult = se(matchToIfThenElse(body))(frame, gctx)

      if(tfd.hasPostcondition) {
        val (id, post) = tfd.postcondition.get

        val freshResID = FreshIdentifier("result").setType(tfd.returnType)
        val postBody = replace(Map(Variable(id) -> Variable(freshResID)), matchToIfThenElse(post))

        se(matchToIfThenElse(post))(frame.withNewVar(id, callResult), gctx) match {
          case BooleanLiteral(true) =>
          case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + tfd.id.name + " reached in evaluation.")
          case other => throw EvalError(typeErrorMsg(other, BooleanType))
        }
      }

      callResult

    case And(args) if args.isEmpty =>
      BooleanLiteral(true)

    case And(args) =>
      se(args.head) match {
        case BooleanLiteral(false) => BooleanLiteral(false)
        case BooleanLiteral(true) => se(And(args.tail))
        case other => throw EvalError(typeErrorMsg(other, BooleanType))
      }

    case Or(args) if args.isEmpty => BooleanLiteral(false)
    case Or(args) =>
      se(args.head) match {
        case BooleanLiteral(true) => BooleanLiteral(true)
        case BooleanLiteral(false) => se(Or(args.tail))
        case other => throw EvalError(typeErrorMsg(other, BooleanType))
      }

    case Not(arg) =>
      se(arg) match {
        case BooleanLiteral(v) => BooleanLiteral(!v)
        case other => throw EvalError(typeErrorMsg(other, BooleanType))
      }

    case Implies(l,r) =>
      (se(l), se(r)) match {
        case (BooleanLiteral(b1),BooleanLiteral(b2)) => BooleanLiteral(!b1 || b2)
        case (le, re) => throw EvalError(typeErrorMsg(le, BooleanType))
      }

    case Iff(le,re) =>
      (se(le), se(re)) match {
        case (BooleanLiteral(b1),BooleanLiteral(b2)) => BooleanLiteral(b1 == b2)
        case _ => throw EvalError(typeErrorMsg(le, BooleanType))
      }
    case Equals(le,re) =>
      val lv = se(le)
      val rv = se(re)

      (lv,rv) match {
        case (FiniteSet(el1),FiniteSet(el2)) => BooleanLiteral(el1.toSet == el2.toSet)
        case (FiniteMap(el1),FiniteMap(el2)) => BooleanLiteral(el1.toSet == el2.toSet)
        case _ => BooleanLiteral(lv == rv)
      }

    case CaseClass(cd, args) =>
      CaseClass(cd, args.map(se(_)))

    case CaseClassInstanceOf(cct, expr) =>
      val le = se(expr)
      BooleanLiteral(le.getType match {
        case CaseClassType(cd2, _) if cd2 == cct.classDef => true
        case _ => false
      })

    case CaseClassSelector(ct1, expr, sel) =>
      val le = se(expr)
      le match {
        case CaseClass(ct2, args) if ct1 == ct2 => args(ct1.classDef.selectorID2Index(sel))
        case _ => throw EvalError(typeErrorMsg(le, ct1))
      }

    case Plus(l,r) =>
      (se(l), se(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case Minus(l,r) =>
      (se(l), se(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case UMinus(e) =>
      se(e) match {
        case IntLiteral(i) => IntLiteral(-i)
        case re => throw EvalError(typeErrorMsg(re, Int32Type))
      }

    case Times(l,r) =>
      (se(l), se(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case Division(l,r) =>
      (se(l), se(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) =>
          if(i2 != 0) IntLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case Modulo(l,r) =>
      (se(l), se(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => 
          if(i2 != 0) IntLiteral(i1 % i2) else throw RuntimeError("Modulo by 0.")
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }
    case LessThan(l,r) =>
      (se(l), se(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 < i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case GreaterThan(l,r) =>
      (se(l), se(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case LessEquals(l,r) =>
      (se(l), se(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case GreaterEquals(l,r) =>
      (se(l), se(r)) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case SetUnion(s1,s2) =>
      (se(s1), se(s2)) match {
        case (f@FiniteSet(els1),FiniteSet(els2)) => FiniteSet((els1 ++ els2).distinct).setType(f.getType)
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetIntersection(s1,s2) =>
      (se(s1), se(s2)) match {
        case (f @ FiniteSet(els1), FiniteSet(els2)) => {
          val newElems = (els1.toSet intersect els2.toSet).toSeq
          val baseType = f.getType.asInstanceOf[SetType].base
          FiniteSet(newElems).setType(f.getType)
        }
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case SetDifference(s1,s2) =>
      (se(s1), se(s2)) match {
        case (f @ FiniteSet(els1),FiniteSet(els2)) => {
          val newElems = (els1.toSet -- els2.toSet).toSeq
          val baseType = f.getType.asInstanceOf[SetType].base
          FiniteSet(newElems).setType(f.getType)
        }
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }

    case ElementOfSet(el,s) => (se(el), se(s)) match {
      case (e, f @ FiniteSet(els)) => BooleanLiteral(els.contains(e))
      case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
    }
    case SubsetOf(s1,s2) => (se(s1), se(s2)) match {
      case (f@FiniteSet(els1),FiniteSet(els2)) => BooleanLiteral(els1.toSet.subsetOf(els2.toSet))
      case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
    }
    case SetCardinality(s) => {
      val sr = se(s)
      sr match {
        case FiniteSet(els) => IntLiteral(els.size)
        case _ => throw EvalError(typeErrorMsg(sr, SetType(AnyType)))
      }
    }

    case f @ FiniteSet(els) => FiniteSet(els.map(se(_)).distinct).setType(f.getType)
    case i @ IntLiteral(_) => i
    case b @ BooleanLiteral(_) => b
    case u @ UnitLiteral => u

    case f @ ArrayFill(length, default) => {
      val rDefault = se(default)
      val rLength = se(length)
      val IntLiteral(iLength) = rLength
      FiniteArray((1 to iLength).map(_ => rDefault).toSeq)
    }
    case ArrayLength(a) => {
      var ra = se(a)
      while(!ra.isInstanceOf[FiniteArray])
        ra = ra.asInstanceOf[ArrayUpdated].array
      IntLiteral(ra.asInstanceOf[FiniteArray].exprs.size)
    }
    case ArrayUpdated(a, i, v) => {
      val ra = se(a)
      val ri = se(i)
      val rv = se(v)

      val IntLiteral(index) = ri
      val FiniteArray(exprs) = ra
      FiniteArray(exprs.updated(index, rv))
    }
    case ArraySelect(a, i) => {
      val IntLiteral(index) = se(i)
      val FiniteArray(exprs) = se(a)
      try {
        exprs(index)
      } catch {
        case e : IndexOutOfBoundsException => throw RuntimeError(e.getMessage)
      }
    }
    case FiniteArray(exprs) => {
      FiniteArray(exprs.map(e => se(e)))
    }

    case f @ FiniteMap(ss) => FiniteMap(ss.map{ case (k, v) => (se(k), se(v)) }.distinct).setType(f.getType)
    case g @ MapGet(m,k) => (se(m), se(k)) match {
      case (FiniteMap(ss), e) => ss.find(_._1 == e) match {
        case Some((_, v0)) => v0
        case None => throw RuntimeError("Key not found: " + e)
      }
      case (l,r) => throw EvalError(typeErrorMsg(l, MapType(r.getType, g.getType)))
    }
    case u @ MapUnion(m1,m2) => (se(m1), se(m2)) match {
      case (f1@FiniteMap(ss1), FiniteMap(ss2)) => {
        val filtered1 = ss1.filterNot(s1 => ss2.exists(s2 => s2._1 == s1._1))
        val newSs = filtered1 ++ ss2
        FiniteMap(newSs).setType(f1.getType)
      }
      case (l, r) => throw EvalError(typeErrorMsg(l, m1.getType))
    }
    case i @ MapIsDefinedAt(m,k) => (se(m), se(k)) match {
      case (FiniteMap(ss), e) => BooleanLiteral(ss.exists(_._1 == e))
      case (l, r) => throw EvalError(typeErrorMsg(l, m.getType))
    }
    case Distinct(args) => {
      val newArgs = args.map(se(_))
      BooleanLiteral(newArgs.distinct.size == newArgs.size)
    }

    case gv: GenericValue =>
      gv

    case choose: Choose =>
      import solvers.z3.FairZ3Solver
      import purescala.TreeOps.simplestValue

      implicit val debugSection = DebugSectionSynthesis

      val p = synthesis.Problem.fromChoose(choose)

      ctx.reporter.debug("Executing choose!")

      val tStart = System.currentTimeMillis;

      val solver = (new FairZ3Solver(ctx, program) with TimeoutSolver).setTimeout(10000L)

      val inputsMap = p.as.map {
        case id =>
          Equals(Variable(id), rctx.mappings(id))
      }

      solver.assertCnstr(And(Seq(p.pc, p.phi) ++ inputsMap))

      try {
        solver.check match {
          case Some(true) =>
            val model = solver.getModel;

            val valModel = valuateWithModel(model) _

            val res = p.xs.map(valModel)
            val leonRes = if (res.size > 1) {
              Tuple(res)
            } else {
              res(0)
            }

            val total = System.currentTimeMillis-tStart;

            ctx.reporter.debug("Synthesis took "+total+"ms")
            ctx.reporter.debug("Finished synthesis with "+leonRes)

            leonRes
          case Some(false) =>
            throw RuntimeError("Constraint is UNSAT")
          case _ =>
            throw RuntimeError("Timeout exceeded")
        }
      } finally {
        solver.free()
      }

    case other => {
      context.reporter.error("Error: don't know how to handle " + other + " in Evaluator.")
      throw EvalError("Unhandled case in Evaluator : " + other) 
    }
  }

  def typeErrorMsg(tree : Expr, expected : TypeTree) : String = "Type error : expected %s, found %s.".format(expected, tree)

  // quick and dirty.. don't overuse.
  private def isGround(expr: Expr) : Boolean = {
    variablesOf(expr) == Set.empty
  }
}
