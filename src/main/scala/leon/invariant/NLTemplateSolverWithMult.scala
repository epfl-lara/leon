package leon
package invariant

import scala.util.Random
import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.ListValue
import leon.Reporter
import leon.verification.DefaultTactic
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.solvers.SimpleSolverAPI
import leon.solvers.z3.UIFZ3Solver
import leon.invariant._
import leon.purescala.UndirectedGraph
import scala.util.control.Breaks._
import leon.solvers._
import leon.purescala.ScalaPrinter
import leon.plugin.DepthInstPhase

class NLTemplateSolverWithMult(context: LeonContext, program: Program, rootFun: FunDef,
  ctrTracker: ConstraintTracker, tempFactory: TemplateFactory, timeout: Int, tightBounds: Boolean) 
  extends NLTemplateSolver(context, program, rootFun, ctrTracker, tempFactory, timeout, tightBounds) {
 
  override def generateCtrsFromDisjunct(fd: FunDef, model: Map[Identifier, Expr]): ((Expr, Set[Call]), Expr) = {

    val formula = ctrTracker.getVC(fd)
    //this picks the satisfiable disjunct of the VC modulo axioms
    val satCtrs = formula.pickSatDisjunct(formula.firstRoot, model)
    //for debugging        
    if (this.debugChooseDisjunct || this.printPathToConsole || this.dumpPathAsSMTLIB) {
      val pathctrs = satCtrs.map(_.toExpr)
      val plainFormula = And(pathctrs)
      val pathcond = simplifyArithmetic(plainFormula)

      if (this.debugChooseDisjunct) {
        satCtrs.filter(_.isInstanceOf[LinearConstraint]).map(_.toExpr).foreach((ctr) => {
          if (!doesSatisfyModel(ctr, model))
            throw IllegalStateException("Path ctr not satisfied by model: " + ctr)
        })
      }

      if (this.verifyInvariant) {
        println("checking invariant for path...")
        Util.checkInvariant(pathcond, context, program)
      }

      if (this.printPathToConsole) {
        //val simpcond = ExpressionTransformer.unFlatten(pathcond, variablesOf(pathcond).filterNot(TVarFactory.isTemporary _))
        val simpcond = pathcond
        println("Full-path: " + ScalaPrinter(simpcond))
        val filename = "full-path-" + FileCountGUID.getID + ".txt"
        val wr = new PrintWriter(new File(filename))
        ExpressionTransformer.PrintWithIndentation(wr, simpcond)
        println("Printed to file: " + filename)
        wr.flush()
        wr.close()
      }

      if (this.dumpPathAsSMTLIB) {
        val filename = "pathcond" + FileCountGUID.getID + ".smt2"
        Util.toZ3SMTLIB(pathcond, filename, "QF_NIA", context, program)
        println("Path dumped to: " + filename)
      }
    }

    var calls = Set[Call]()
    var cons = Set[Expr]()
    satCtrs.foreach(ctr => ctr match {
      case t: Call => calls += t
      case t: ADTConstraint if (t.cons.isDefined) => cons += t.cons.get
      case _ => ;
    })
    val callExprs = calls.map(_.toExpr)

    //reporter.info("choosing axioms...")
    var t1 = System.currentTimeMillis()
    val axiomCtrs = ctrTracker.specInstantiator.axiomsForCalls(formula, calls, model)
    var t2 = System.currentTimeMillis()
    //reporter.info("chosen axioms...in " + (t2 - t1) / 1000.0 + "s")
    Stats.updateCumTime((t2 - t1), "Total-AxiomChoose-Time")

    //for stats
    //reporter.info("starting UF/ADT elimination...")
    t1 = System.currentTimeMillis()
    val callCtrs = (new UFADTEliminator(context, program)).constraintsForCalls((callExprs ++ cons), model).map(ConstraintUtil.createConstriant _)
    t2 = System.currentTimeMillis()
    //reporter.info("completed UF/ADT elimination...in " + (t2 - t1) / 1000.0 + "s")
    Stats.updateCumTime((t2 - t1), "Total-ElimUF-Time")

    //exclude guards, separate calls and cons from the rest
    var lnctrs = Set[LinearConstraint]()
    var temps = Set[LinearTemplate]()
    (satCtrs ++ callCtrs ++ axiomCtrs).foreach(ctr => ctr match {
      case t: LinearConstraint => lnctrs += t
      case t: LinearTemplate => temps += t
      case _ => ;
    })

    if (this.debugChooseDisjunct) {
      lnctrs.map(_.toExpr).foreach((ctr) => {
        if (!doesSatisfyModel(ctr, model))
          throw IllegalStateException("Ctr not satisfied by model: " + ctr)
      })
    }

    val (data, nlctr) = processNumCtrs(lnctrs.toSeq, temps.toSeq)
    ((data, calls), nlctr)
  }
}
