package orderedsets

import purescala.Reporter
import purescala.Extensions.Solver
import Reconstruction.Model
import purescala.Trees._
import purescala.Common._
import purescala.Definitions._

object Unifier {
  case class UnifierException(str: String) extends Exception(str)
     
  private def makeConstr(arg1: Seq[Expr], arg2: Seq[Expr]): Seq[Equals] = {
    arg1.zip(arg2).map(x => Equals(x._1,x._2))
  }

  private def unify(constr: Seq[Expr]) : Map[Variable, Expr] =
    if(constr.isEmpty) Map.empty
    else constr.head match {
      case Equals(Variable(id1), Variable(id2)) if id1 == id2 => unify(constr.tail)
      case Equals(t1, t2) if t1 == t2 => unify(constr.tail)
      case Equals(v @ Variable(id1), tr) => unifyBaseCase(v, tr, constr.tail)
      case Equals(tr, v @ Variable(id1)) => unifyBaseCase(v, tr, constr.tail)
      case Equals(a @ CaseClass(cc1, args1), b @ CaseClass(cc2, args2) ) if (cc1 == cc2) => unify( makeConstr(args1, args2) ++ constr.tail)
      case Equals(a, b) => throw(new UnifierException("Cannot unify " + a + " and " + b ))
      case _ => throw(new UnifierException("Illegal expression in unifier: " + constr.head))
    }

  private def transform(v: Variable, substVal: Expr)(t: Expr): Expr = t match {
    case v1 @ Variable(_) if v1 == v => substVal
    case CaseClassSelector(t1, selector) if t1 == v => CaseClassSelector(substVal, selector)
    case CaseClass(cc, args) => CaseClass(cc, args map transform(v, substVal))
    case _ => t
  }

  private def unifyBaseCase(v: Variable, t1: Expr, rest: Seq[Expr]) = {
    val subst = transform(v, t1) _
    val substitutedTail = rest.map( {case Equals(t1, t2) => Equals(subst(t1), subst(t2)); case t => throw(new UnifierException("Cannot handle expression: " + t)) } )
    unify(substitutedTail).updated(v, t1)
  }

  def unify(form : And) : And = {
    val And(constraints) = form
    val equalConstr = constraints.filter( {case Equals(_,_) => true; case _ => false} )
    val notEqualConstr =  constraints.filter( {case Not(Equals(_,_)) => true; case _ => false} )
    val varMap = unify( equalConstr )
    And(varMap.map( x => Equals(x._1, x._2) ).toList)
  }

  def main(args: Array[String]) = {
    val CC1 = new CaseClassDef(FreshIdentifier("Node"))
    val a = Variable(FreshIdentifier("a"))
    val b = Variable(FreshIdentifier("b"))
    val c = Variable(FreshIdentifier("c"))
    val CC1_inst = CaseClass(CC1, List(a))

    val eq1 = Equals(CC1_inst, b)
    val eq2 = Equals(CaseClass(CC1, List(c)), b)
    val form = unify( And( List(eq1, eq2) ) )
    println(form)
  }
}

