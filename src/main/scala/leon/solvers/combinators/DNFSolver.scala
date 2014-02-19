/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

class DNFSolver(val context: LeonContext,
                underlyings: SolverFactory[Solver]) extends Solver {

  def name = "DNF("+underlyings.name+")"

  def free {}

  private var theConstraint : Option[Expr] = None
  private var theModel : Option[Map[Identifier,Expr]] = None

  import context.reporter._

  def assertCnstr(expression : Expr) {
    if(!theConstraint.isEmpty) { fatalError("Multiple assertCnstr(...).") }
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
    val vs : Set[Identifier] = theConstraint.map(variablesOf(_)).getOrElse(Set.empty)
    theModel.getOrElse(Map.empty).filter(p => vs(p._1))
  }

  private def nnf(expr : Expr, flip : Boolean) : Expr = expr match {
    case _ : Let | _ : IfExpr => throw new Exception("Can't NNF *everything*, sorry.")
    case Not(Implies(l,r)) => nnf(And(l, Not(r)), flip)
    case Implies(l, r)     => nnf(Or(Not(l), r), flip)
    case Not(Iff(l, r))    => nnf(Or(And(l, Not(r)), And(Not(l), r)), flip)
    case Iff(l, r)         => nnf(Or(And(l, r), And(Not(l), Not(r))), flip)
    case And(es) if flip   => Or(es.map(e => nnf(e, true)))
    case And(es)           => And(es.map(e => nnf(e, false)))
    case Or(es)  if flip   => And(es.map(e => nnf(e, true)))
    case Or(es)            => Or(es.map(e => nnf(e, false)))
    case Not(e) if flip    => nnf(e, false)
    case Not(e)            => nnf(e, true)
    case LessThan(l,r)      if flip => GreaterEquals(l,r)
    case GreaterThan(l,r)   if flip => LessEquals(l,r)
    case LessEquals(l,r)    if flip => GreaterThan(l,r)
    case GreaterEquals(l,r) if flip => LessThan(l,r)
    case elze if flip      => Not(elze)
    case elze              => elze
  }

  // fun pushC (And(p,Or(q,r))) = Or(pushC(And(p,q)),pushC(And(p,r)))
  //   | pushC (And(Or(q,r),p)) = Or(pushC(And(p,q)),pushC(And(p,r)))
  //   | pushC (And(p,q))       = And(pushC(p),pushC(q))
  //   | pushC (Literal(l))     = Literal(l)
  //   | pushC (Or(p,q))        = Or(pushC(p),pushC(q))

  private def dnf(expr : Expr) : Expr = expr match {
    case And(es) =>
      val (ors, lits) = es.partition(_.isInstanceOf[Or])
      if(!ors.isEmpty) {
        val orHead = ors.head.asInstanceOf[Or]
        val orTail = ors.tail
        Or(orHead.exprs.map(oe => dnf(And(filterObvious(lits ++ (oe +: orTail))))))
      } else {
        expr
      }

    case Or(es) =>
      Or(es.map(dnf(_)))

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
    if(!both.isEmpty) {
      Seq(BooleanLiteral(false))
    } else {
      exprs
    }
  }
}
