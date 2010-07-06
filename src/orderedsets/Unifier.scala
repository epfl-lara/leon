package orderedsets

import purescala.Reporter
import purescala.Extensions.Solver
import Reconstruction.Model
import purescala.Trees._
import purescala.Common._
import purescala.Definitions._

object Unifier {
  case class UnifierException(str: String) extends Exception(str)
     
  private def makeConstr(arg1: Seq[Expr], arg2: Seq[Expr]): List[Equals] = {
    arg1.zip(arg2).map(x => Equals(x._1,x._2)).toList
  }

  private def notOccurs(v : Variable)(tr: Expr): Boolean = tr match {
    case v2 @ Variable(_) if v2 == v => false
    case Variable(_) => true
    case CaseClassSelector( t1, _ ) => notOccurs(v)(t1)
    case CaseClass(_, args) => (true /: args) {_ && notOccurs(v)(_)}
    case _ => throw(new UnifierException("Cannot handle expression : " + tr))
  }

  private def unify(constr: List[Expr]) : Map[Variable, Expr] =
    if(constr.isEmpty) Map.empty
    else constr.head match {
      case Equals(Variable(id1), Variable(id2)) if id1 == id2 => unify(constr.tail)
      case Equals(t1, t2) if t1 == t2 => unify(constr.tail)
      case Equals(v @ Variable(id1), tr) if notOccurs(v)(tr) => unifyBaseCase(v, tr, constr.tail)
      case Equals(tr, v @ Variable(id1)) if notOccurs(v)(tr) => unifyBaseCase(v, tr, constr.tail)
      case Equals(cc @ CaseClassSelector(t1, fld), tr) => {
        val freshVar1 = Variable(FreshIdentifier("unifVar", true)).setType(cc.getType)
        val freshVar2 = Variable(FreshIdentifier("unifVar", true)).setType(cc.getType)
        unify( Equals(freshVar1, cc) :: Equals(freshVar2, tr) :: constr ).updated(freshVar1, freshVar2)
      }
      case Equals(tr, cc @ CaseClassSelector(t1, fld)) => {
        val freshVar1 = Variable(FreshIdentifier("unifVar", true)).setType(cc.getType)
        val freshVar2 = Variable(FreshIdentifier("unifVar", true)).setType(cc.getType)
        unify( Equals(freshVar1, cc) :: Equals(freshVar2, tr) :: constr ).updated(freshVar1, freshVar2)
      }case Equals(a @ CaseClass(cc1, args1), b @ CaseClass(cc2, args2) ) if (cc1 == cc2) => unify( makeConstr(args1, args2) ++ constr.tail)
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
    val substitutedTail = rest.map( {case Equals(t1, t2) => Equals(subst(t1), subst(t2)); case t => throw(new UnifierException("Cannot handle expression: " + t)) } ).toList
    unify(substitutedTail).updated(v, t1)
  }

  private def recSubst(varMap: Map[Variable, Expr], tr: Expr): Expr = tr match {
    case v @ Variable(_) if varMap.contains(v) => recSubst(varMap, varMap(v))
    case Variable(_) => tr
    case CaseClassSelector(tr, fld) => CaseClassSelector(recSubst(varMap, tr), fld)
    case CaseClass(cc, args) => CaseClass(cc, args map (x => recSubst(varMap, x)))
    case _ => throw(new UnifierException("Unifier cannot handle: " + tr))
  }

  private def isInEqSatisfied(varMap: Map[Variable, Expr], inEq: Seq[Expr]): Boolean = if(inEq.isEmpty) true
    else inEq.head match {
      case Not(Equals(t1, t2)) if (recSubst(varMap, t1) == recSubst(varMap, t2)) => false
      case _ => isInEqSatisfied(varMap, inEq.tail)
    }

  def unify(form : And) : And = {
    val And(constraints) = form
    val equalConstr = constraints.filter( {case Equals(_,_) => true; case _ => false} )
    val notEqualConstr =  constraints.filter( {case Not(Equals(_,_)) => true; case _ => false} )
    val varMap = unify(equalConstr.toList)
    if(isInEqSatisfied(varMap, notEqualConstr)) And(varMap.map( x => Equals(x._1, x._2) ).toList)
    else throw(new UnifierException("Inequality constraints cannot be satisfied."))
  }

  def main(args: Array[String]) = {
    val CC1 = new CaseClassDef(FreshIdentifier("Node"))
    val a = Variable(FreshIdentifier("a"))
    val b = Variable(FreshIdentifier("b"))
    val c = Variable(FreshIdentifier("c"))
    val CC1_inst = CaseClass(CC1, List(a))

    val eq1 = Equals(CC1_inst, b)
    val eq2 = Equals(CaseClass(CC1, List(c)), b)
    var form =  And( List(eq1, eq2) ) 
    var res = unify(form)
    println("Formula = " + form)
    println("Result = " + res)
    println()

    // Fails occurs check
    val eq3 = Equals(CC1_inst, c)
    try {
      form =  And( List(eq1, eq2, eq3) ) 
      println("Formula = " + form)
      res = unify(form)
      println("Result = " + res)
      println()
    } catch {
      case e => println("Exception: " + e)
    }

    val eq4 = Not(Equals(a, c))
    try {
      form =  And( List(eq1, eq2, eq4) ) 
      println("Formula = " + form)
      res = unify(form)
      println("Result = " + res)
      println()
    } catch {
      case e => println("Exception: " + e)
    }
  }

}

