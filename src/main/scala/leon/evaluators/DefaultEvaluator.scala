/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._
import purescala.TypeTrees._

import xlang.Trees._

class DefaultEvaluator(ctx : LeonContext, prog : Program) extends Evaluator(ctx, prog) {
  val name = "evaluator"
  val description = "Recursive interpreter for PureScala expressions"

  private def typeErrorMsg(tree : Expr, expected : TypeTree) : String = "Type error : expected %s, found %s.".format(expected, tree)
  private case class EvalError(msg : String) extends Exception
  private case class RuntimeError(msg : String) extends Exception

  private val maxSteps = 50000

  def eval(expression: Expr, mapping : Map[Identifier,Expr]) : EvaluationResults.Result = {
    var left: Int = maxSteps

    def rec(ctx: Map[Identifier,Expr], expr: Expr) : Expr = if(left <= 0) {
      throw RuntimeError("Diverging computation.")
    } else {
      // println("Step on : " + expr)
      // println(ctx)
      left -= 1
      expr match {
        case Variable(id) => {
          if(ctx.isDefinedAt(id)) {
            val res = ctx(id)
            if(!isGround(res)) {
              throw EvalError("Substitution for identifier " + id.name + " is not ground.")
            } else {
              res
            }
          } else {
            throw EvalError("No value for identifier " + id.name + " in mapping.")
          }
        }
        case Tuple(ts) => {
          val tsRec = ts.map(rec(ctx, _))
          Tuple(tsRec)
        }
        case TupleSelect(t, i) => {
          val Tuple(rs) = rec(ctx, t)
          rs(i-1)
        }
        case Let(i,e,b) => {
          val first = rec(ctx, e)
          rec(ctx + ((i -> first)), b)
        }
        case Error(desc) => throw RuntimeError("Error reached in evaluation: " + desc)
        case IfExpr(cond, thenn, elze) => {
          val first = rec(ctx, cond)
          first match {
            case BooleanLiteral(true) => rec(ctx, thenn)
            case BooleanLiteral(false) => rec(ctx, elze)
            case _ => throw EvalError(typeErrorMsg(first, BooleanType))
          }
        }
        case Waypoint(_, arg) => rec(ctx, arg)
        case FunctionInvocation(fd, args) => {
          val evArgs = args.map(a => rec(ctx, a))
          // build a mapping for the function...
          val frame = Map[Identifier,Expr]((fd.args.map(_.id) zip evArgs) : _*)
          
          if(fd.hasPrecondition) {
            rec(frame, matchToIfThenElse(fd.precondition.get)) match {
              case BooleanLiteral(true) => ;
              case BooleanLiteral(false) => {
                throw RuntimeError("Precondition violation for " + fd.id.name + " reached in evaluation.: " + fd.precondition.get)
              }
              case other => throw RuntimeError(typeErrorMsg(other, BooleanType))
            }
          }

          if(!fd.hasBody && !mapping.isDefinedAt(fd.id)) {
            throw EvalError("Evaluation of function with unknown implementation.")
          }
          val body = fd.body.getOrElse(mapping(fd.id))
          val callResult = rec(frame, matchToIfThenElse(body))

          if(fd.hasPostcondition) {
            val (id, post) = fd.postcondition.get

            val freshResID = FreshIdentifier("result").setType(fd.returnType)
            val postBody = replace(Map(Variable(id) -> Variable(freshResID)), matchToIfThenElse(post))
            rec(frame + ((freshResID -> callResult)), postBody) match {
              case BooleanLiteral(true) => ;
              case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + fd.id.name + " reached in evaluation.")
              case other => throw EvalError(typeErrorMsg(other, BooleanType))
            }
          }

          callResult
        }
        case And(args) if args.isEmpty => BooleanLiteral(true)
        case And(args) => {
          rec(ctx, args.head) match {
            case BooleanLiteral(false) => BooleanLiteral(false)
            case BooleanLiteral(true) => rec(ctx, And(args.tail))
            case other => throw EvalError(typeErrorMsg(other, BooleanType))
          }
        }
        case Or(args) if args.isEmpty => BooleanLiteral(false)
        case Or(args) => {
          rec(ctx, args.head) match {
            case BooleanLiteral(true) => BooleanLiteral(true)
            case BooleanLiteral(false) => rec(ctx, Or(args.tail))
            case other => throw EvalError(typeErrorMsg(other, BooleanType))
          }
        }
        case Not(arg) => rec(ctx, arg) match {
          case BooleanLiteral(v) => BooleanLiteral(!v)
          case other => throw EvalError(typeErrorMsg(other, BooleanType))
        }
        case Implies(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (BooleanLiteral(b1),BooleanLiteral(b2)) => BooleanLiteral(!b1 || b2)
          case (le,re) => throw EvalError(typeErrorMsg(le, BooleanType))
        }
        case Iff(le,re) => (rec(ctx,le),rec(ctx,re)) match {
          case (BooleanLiteral(b1),BooleanLiteral(b2)) => BooleanLiteral(b1 == b2)
          case _ => throw EvalError(typeErrorMsg(le, BooleanType))
        }
        case Equals(le,re) => {
          val lv = rec(ctx,le)
          val rv = rec(ctx,re)

          (lv,rv) match {
            case (FiniteSet(el1),FiniteSet(el2)) => BooleanLiteral(el1.toSet == el2.toSet)
            case (FiniteMap(el1),FiniteMap(el2)) => BooleanLiteral(el1.toSet == el2.toSet)
            case _ => BooleanLiteral(lv == rv)
          }
        }
        case CaseClass(cd, args) => CaseClass(cd, args.map(rec(ctx,_)))
        case CaseClassInstanceOf(cd, expr) => {
          val le = rec(ctx,expr)
          BooleanLiteral(le.getType match {
            case CaseClassType(cd2) if cd2 == cd => true
            case _ => false
          })
        }
        case CaseClassSelector(cd, expr, sel) => {
          val le = rec(ctx, expr)
          le match {
            case CaseClass(cd2, args) if cd == cd2 => args(cd.selectorID2Index(sel))
            case _ => throw EvalError(typeErrorMsg(le, CaseClassType(cd)))
          }
        }
        case Plus(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
        case Minus(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
        case UMinus(e) => rec(ctx,e) match {
          case IntLiteral(i) => IntLiteral(-i)
          case re => throw EvalError(typeErrorMsg(re, Int32Type))
        }
        case Times(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
        case Division(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) =>
            if(i2 != 0) IntLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
        case Modulo(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => 
            if(i2 != 0) IntLiteral(i1 % i2) else throw RuntimeError("Modulo by 0.")
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
        case LessThan(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 < i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
        case GreaterThan(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
        case LessEquals(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }
        case GreaterEquals(l,r) => (rec(ctx,l), rec(ctx,r)) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
          case (le,re) => throw EvalError(typeErrorMsg(le, Int32Type))
        }

        case SetUnion(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (f@FiniteSet(els1),FiniteSet(els2)) => FiniteSet((els1 ++ els2).distinct).setType(f.getType)
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }
        case SetIntersection(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (f@FiniteSet(els1),FiniteSet(els2)) => {
            val newElems = (els1.toSet intersect els2.toSet).toSeq
            val baseType = f.getType.asInstanceOf[SetType].base
            FiniteSet(newElems).setType(f.getType)
          }
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }
        case SetDifference(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (f@FiniteSet(els1),FiniteSet(els2)) => {
            val newElems = (els1.toSet -- els2.toSet).toSeq
            val baseType = f.getType.asInstanceOf[SetType].base
            FiniteSet(newElems).setType(f.getType)
          }
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }
        case ElementOfSet(el,s) => (rec(ctx,el), rec(ctx,s)) match {
          case (e, f @ FiniteSet(els)) => BooleanLiteral(els.contains(e))
          case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
        }
        case SubsetOf(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
          case (f@FiniteSet(els1),FiniteSet(els2)) => BooleanLiteral(els1.toSet.subsetOf(els2.toSet))
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }
        case SetCardinality(s) => {
          val sr = rec(ctx, s)
          sr match {
            case FiniteSet(els) => IntLiteral(els.size)
            case _ => throw EvalError(typeErrorMsg(sr, SetType(AnyType)))
          }
        }

        case f @ FiniteSet(els) => FiniteSet(els.map(rec(ctx,_)).distinct).setType(f.getType)
        case i @ IntLiteral(_) => i
        case b @ BooleanLiteral(_) => b
        case u @ UnitLiteral => u

        case f @ ArrayFill(length, default) => {
          val rDefault = rec(ctx, default)
          val rLength = rec(ctx, length)
          val IntLiteral(iLength) = rLength
          FiniteArray((1 to iLength).map(_ => rDefault).toSeq)
        }
        case ArrayLength(a) => {
          var ra = rec(ctx, a)
          while(!ra.isInstanceOf[FiniteArray])
            ra = ra.asInstanceOf[ArrayUpdated].array
          IntLiteral(ra.asInstanceOf[FiniteArray].exprs.size)
        }
        case ArrayUpdated(a, i, v) => {
          val ra = rec(ctx, a)
          val ri = rec(ctx, i)
          val rv = rec(ctx, v)

          val IntLiteral(index) = ri
          val FiniteArray(exprs) = ra
          FiniteArray(exprs.updated(index, rv))
        }
        case ArraySelect(a, i) => {
          val IntLiteral(index) = rec(ctx, i)
          val FiniteArray(exprs) = rec(ctx, a)
          try {
            exprs(index)
          } catch {
            case e : IndexOutOfBoundsException => throw RuntimeError(e.getMessage)
          }
        }
        case FiniteArray(exprs) => {
          FiniteArray(exprs.map(e => rec(ctx, e)))
        }

        case f @ FiniteMap(ss) => FiniteMap(ss.map{ case (k, v) => (rec(ctx, k), rec(ctx, v)) }.distinct).setType(f.getType)
        case g @ MapGet(m,k) => (rec(ctx,m), rec(ctx,k)) match {
          case (FiniteMap(ss), e) => ss.find(_._1 == e) match {
            case Some((_, v0)) => v0
            case None => throw RuntimeError("Key not found: " + e)
          }
          case (l,r) => throw EvalError(typeErrorMsg(l, MapType(r.getType, g.getType)))
        }
        case u @ MapUnion(m1,m2) => (rec(ctx,m1), rec(ctx,m2)) match {
          case (f1@FiniteMap(ss1), FiniteMap(ss2)) => {
            val filtered1 = ss1.filterNot(s1 => ss2.exists(s2 => s2._1 == s1._1))
            val newSs = filtered1 ++ ss2
            FiniteMap(newSs).setType(f1.getType)
          }
          case (l, r) => throw EvalError(typeErrorMsg(l, m1.getType))
        }
        case i @ MapIsDefinedAt(m,k) => (rec(ctx,m), rec(ctx,k)) match {
          case (FiniteMap(ss), e) => BooleanLiteral(ss.exists(_._1 == e))
          case (l, r) => throw EvalError(typeErrorMsg(l, m.getType))
        }
        case Distinct(args) => {
          val newArgs = args.map(rec(ctx, _))
          BooleanLiteral(newArgs.distinct.size == newArgs.size)
        } 

        case Choose(_, _) =>
          throw EvalError("Cannot evaluate choose.")

        case other => {
          context.reporter.error("Error: don't know how to handle " + other + " in Evaluator.")
          throw EvalError("Unhandled case in Evaluator : " + other) 
        }
      }
    }

    try {
      EvaluationResults.Successful(rec(mapping, expression))
    } catch {
      case so: StackOverflowError =>
        EvaluationResults.EvaluatorError("Stack overflow")
      case EvalError(msg) =>
        EvaluationResults.EvaluatorError(msg)
      case RuntimeError(msg) =>
        EvaluationResults.RuntimeError(msg)
    }
  }

  // quick and dirty.. don't overuse.
  private def isGround(expr: Expr) : Boolean = {
    variablesOf(expr) == Set.empty
  }
}
