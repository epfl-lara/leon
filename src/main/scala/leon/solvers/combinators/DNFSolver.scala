/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._

class DNFSolver(val context: LeonContext,
                underlyings: SolverFactory[Solver]) extends Solver {

  def name = "DNF("+underlyings.name+")"

  def free() {}

  private var theConstraint : Option[Expr] = None
  private var theModel : Option[Map[Identifier,Expr]] = None

  import context.reporter._

  def assertCnstr(expression : Expr) {
    if(theConstraint.isDefined) { fatalError("Multiple assertCnstr(...).") }
    theConstraint = Some(expression)
  }

  def check : Option[Boolean] = theConstraint.map { expr =>

    val simpleSolver = SimpleSolverAPI(underlyings)

    var result : Option[Boolean] = None

    debugS("Before NNF:\n" + expr.asString)

    val nnfed = nnf(expr, false)

    debugS("After NNF:\n" + nnfed.asString)

    val dnfed = dnf(nnfed)

    debugS("After DNF:\n" + dnfed.asString)

    val candidates : Seq[Expr] = dnfed match {
      case Or(es) => es
      case elze => Seq(elze)
    }

    debugS("# conjuncts : " + candidates.size)

    var done : Boolean = false

    for(candidate <- candidates if !done) {
      simpleSolver.solveSAT(candidate) match {
        case (Some(false), _) =>
          result = Some(false)

        case (Some(true), m) =>
          result = Some(true)
          theModel = Some(m)
          done = true

        case (None, m) =>
          result = None
          theModel = Some(m)
          done = true
       }
    }
    result
  } getOrElse {
    Some(true)
  }

  def getModel : Map[Identifier,Expr] = {
    val vs : Set[Identifier] = theConstraint.map(variablesOf).getOrElse(Set.empty)
    theModel.getOrElse(Map.empty).filter(p => vs(p._1))
  }

  private def nnf(expr : Expr, flip : Boolean) : Expr = expr match {
    case _ : Let | _ : IfExpr => throw new Exception("Can't NNF *everything*, sorry.")
    case Not(Implies(l,r)) => nnf(and(l, not(r)), flip)
    case Implies(l, r)     => nnf(or(not(l), r), flip)
    case Not(Equals(l, r)) => nnf(or(and(l, not(r)), and(not(l), r)), flip)
    case Equals(l, r)      => nnf(or(and(l, r), and(not(l), not(r))), flip)
    case And(es) if flip   => orJoin(es.map(e  => nnf(e, true)))
    case And(es)           => andJoin(es.map(e => nnf(e, false)))
    case Or(es)  if flip   => andJoin(es.map(e => nnf(e, true)))
    case Or(es)            => orJoin(es.map(e  => nnf(e, false)))
    case Not(e) if flip    => nnf(e, false)
    case Not(e)            => nnf(e, true)
    case LessThan(l,r)      if flip => GreaterEquals(l,r)
    case GreaterThan(l,r)   if flip => LessEquals(l,r)
    case LessEquals(l,r)    if flip => GreaterThan(l,r)
    case GreaterEquals(l,r) if flip => LessThan(l,r)
    case elze if flip      => not(elze)
    case elze              => elze
  }

  private def dnf(expr : Expr) : Expr = expr match {
    case And(es) =>
      val (ors, lits) = es.partition(_.isInstanceOf[Or])
      if(ors.nonEmpty) {
        val orHead = ors.head.asInstanceOf[Or]
        val orTail = ors.tail
        orJoin(orHead.exprs.map(oe => dnf(andJoin(filterObvious(lits ++ (oe +: orTail))))))
      } else {
        expr
      }

    case Or(es) =>
      orJoin(es.map(dnf))

    case _ => expr
  }

  private def filterObvious(exprs : Seq[Expr]) : Seq[Expr] = {
    var pos : List[Identifier] = Nil
    var neg : List[Identifier] = Nil

    for(e <- exprs) e match {
      case Variable(id)      => pos = id :: pos
      case Not(Variable(id)) => neg = id :: neg
      case _ => ;
    }

    val both : Set[Identifier] = pos.toSet intersect neg.toSet
    if(both.nonEmpty) {
      Seq(BooleanLiteral(false))
    } else {
      exprs
    }
  }
}
