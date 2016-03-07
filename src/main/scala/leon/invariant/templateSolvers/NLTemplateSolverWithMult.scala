/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.templateSolvers

import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors._
import solvers._

import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.structure._
import Util._
import PredicateUtil._

class NLTemplateSolverWithMult(ctx: InferenceContext, program: Program, rootFun: FunDef,
                               ctrTracker: ConstraintTracker, minimizer: Option[(Expr, Model) => Model])
    extends NLTemplateSolver(ctx, program, rootFun, ctrTracker, minimizer) {

  throw new IllegalStateException("Not Maintained!!")
//  val axiomFactory = new AxiomFactory(ctx)
//
//  override def getVCForFun(fd: FunDef): Expr = {
//    val plainvc = ctrTracker.getVC(fd).toExpr
//    val nlvc = multToTimes(plainvc)
//    nlvc
//  }
//
//  override def splitVC(fd: FunDef) = {
//    val (paramPart, rest, modCons) = super.splitVC(fd) 
//    (multToTimes(paramPart), multToTimes(rest), modCons)
//  }
//
//  override def axiomsForTheory(formula: Formula, calls: Set[Call], model: LazyModel): Seq[Constraint] = {
//
//    //in the sequel we instantiate axioms for multiplication
//    val inst1 = unaryMultAxioms(formula, calls, linearEval.predEval(model))
//    val inst2 = binaryMultAxioms(formula, calls, linearEval.predEval(model))
//    val multCtrs = (inst1 ++ inst2).flatMap {
//      case And(args) => args.map(ConstraintUtil.createConstriant _)
//      case e         => Seq(ConstraintUtil.createConstriant(e))
//    }
//
//    Stats.updateCounterStats(multCtrs.size, "MultAxiomBlowup", "disjuncts")
//    ctx.reporter.info("Number of multiplication induced predicates: " + multCtrs.size)
//    multCtrs
//  }
//
//  def chooseSATPredicate(expr: Expr, predEval: (Expr => Option[Boolean])): Expr = {
//    val norme = ExpressionTransformer.normalizeExpr(expr, ctx.multOp)
//    val preds = norme match {
//      case Or(args)       => args
//      case Operator(_, _) => Seq(norme)
//      case _              => throw new IllegalStateException("Not(ant) is not in expected format: " + norme)
//    }
//    //pick the first predicate that holds true
//    preds.collectFirst { case pred @ _ if predEval(pred).get => pred }.get
//  }
//
//  def isMultOp(call: Call): Boolean = {
//    isMultFunctions(call.fi.tfd.fd)
//  }
//
//  def unaryMultAxioms(formula: Formula, calls: Set[Call], predEval: (Expr => Option[Boolean])): Seq[Expr] = {
//    val axioms = calls.flatMap {
//      case call @ _ if (isMultOp(call) && axiomFactory.hasUnaryAxiom(call)) => {
//        val (ant, conseq) = axiomFactory.unaryAxiom(call)
//        if (predEval(ant).get)
//          Seq(ant, conseq)
//        else
//          Seq(chooseSATPredicate(Not(ant), predEval))
//      }
//      case _ => Seq()
//    }
//    axioms.toSeq
//  }
//
//  def binaryMultAxioms(formula: Formula, calls: Set[Call], predEval: (Expr => Option[Boolean])): Seq[Expr] = {
//
//    val mults = calls.filter(call => isMultOp(call) && axiomFactory.hasBinaryAxiom(call))
//    val product = cross(mults, mults).collect { case (c1, c2) if c1 != c2 => (c1, c2) }
//
//    ctx.reporter.info("Theory axioms: " + product.size)
//    Stats.updateCumStats(product.size, "-Total-theory-axioms")
//
//    val newpreds = product.flatMap(pair => {
//      val axiomInsts = axiomFactory.binaryAxiom(pair._1, pair._2)
//      axiomInsts.flatMap {
//        case (ant, conseq) if predEval(ant).get => Seq(ant, conseq) //if axiom-pre holds.
//        case (ant, _)                           => Seq(chooseSATPredicate(Not(ant), predEval)) //if axiom-pre does not hold.
//      }
//    })
//    newpreds.toSeq
//  }
}
