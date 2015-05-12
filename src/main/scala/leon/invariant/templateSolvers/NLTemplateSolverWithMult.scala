package leon
package invariant.templateSolvers
import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import leon.invariant._
import scala.util.control.Breaks._
import solvers._

import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.structure._

class NLTemplateSolverWithMult(ctx : InferenceContext, rootFun: FunDef,
  ctrTracker: ConstraintTracker, minimizer: Option[(Expr, Model) => Model])
  extends NLTemplateSolver(ctx, rootFun, ctrTracker, minimizer) {

  val axiomFactory = new AxiomFactory(ctx)

  override def getVCForFun(fd: FunDef): Expr = {
    val plainvc = ctrTracker.getVC(fd).toExpr
    val nlvc = Util.multToTimes(plainvc)
    nlvc
  }

  override def splitVC(fd: FunDef) : (Expr,Expr) = {
    val (paramPart, rest) = ctrTracker.getVC(fd).splitParamPart
    (Util.multToTimes(paramPart),Util.multToTimes(rest))
  }

  override def axiomsForTheory(formula : Formula, calls: Set[Call], model: Model) : Seq[Constraint] = {

    //in the sequel we instantiate axioms for multiplication
    val inst1 = unaryMultAxioms(formula, calls, predEval(model))
    val inst2 = binaryMultAxioms(formula,calls, predEval(model))
    val multCtrs = (inst1 ++ inst2).flatMap(_ match {
      case And(args) => args.map(ConstraintUtil.createConstriant _)
      case e => Seq(ConstraintUtil.createConstriant(e))
    })

    Stats.updateCounterStats(multCtrs.size, "MultAxiomBlowup", "disjuncts")
    ctx.reporter.info("Number of multiplication induced predicates: "+multCtrs.size)
    multCtrs
  }

  def chooseSATPredicate(expr: Expr, predEval: (Expr => Boolean)): Expr = {
    val norme = ExpressionTransformer.normalizeExpr(expr,ctx.multOp)
    val preds = norme match {
      case Or(args) => args
      case Operator(_, _) => Seq(norme)
      case _ => throw new IllegalStateException("Not(ant) is not in expected format: " + norme)
    }
    //pick the first predicate that holds true
    preds.collectFirst { case pred @ _ if predEval(pred) => pred }.get
  }

  def isMultOp(call : Call) : Boolean = {
    Util.isMultFunctions(call.fi.tfd.fd)
  }

  def unaryMultAxioms(formula: Formula, calls: Set[Call], predEval: (Expr => Boolean)) : Seq[Expr] = {
    val axioms = calls.flatMap {
      case call@_ if (isMultOp(call) && axiomFactory.hasUnaryAxiom(call)) => {
        val (ant,conseq) = axiomFactory.unaryAxiom(call)
        if(predEval(ant))
          Seq(ant,conseq)
        else
          Seq(chooseSATPredicate(Not(ant), predEval))
      }
      case _ => Seq()
    }
    axioms.toSeq
  }

  def binaryMultAxioms(formula: Formula, calls: Set[Call], predEval: (Expr => Boolean)) : Seq[Expr] = {

    val mults = calls.filter(call => isMultOp(call) && axiomFactory.hasBinaryAxiom(call))
    val product = Util.cross(mults,mults).collect{ case (c1,c2) if c1 != c2 => (c1,c2) }

    ctx.reporter.info("Theory axioms: "+product.size)
    Stats.updateCumStats(product.size, "-Total-theory-axioms")

    val newpreds = product.flatMap(pair => {
      val axiomInsts = axiomFactory.binaryAxiom(pair._1, pair._2)
      axiomInsts.flatMap {
        case (ant,conseq) if predEval(ant) => Seq(ant,conseq) 			//if axiom-pre holds.
        case (ant,_) => Seq(chooseSATPredicate(Not(ant), predEval))		//if axiom-pre does not hold.
      }
    })
    newpreds.toSeq
  }
}
