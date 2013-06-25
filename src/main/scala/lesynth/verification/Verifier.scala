package lesynth

import leon.solvers._
import leon.purescala.Common._
import leon.purescala.Trees._
import leon.purescala.Extractors._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._
import leon.purescala.Definitions._
import leon.synthesis._

import insynth.util.logging._

class Verifier(solver: IncrementalSolver, p: Problem, synthInfo: SynthesisInfo = new SynthesisInfo)
	extends AbstractVerifier(solver, p, synthInfo) with HasLogger {
    
  import SynthesisInfo.Action._
  
  override def checkValidity(expression: Expr) = {
    solver.assertCnstr(Not(expression))   
    val solverCheckResult = solver.check
    fine("Solver said " + solverCheckResult + " for " + expression)
    solverCheckResult match {
      case Some(true) =>
        false
      case Some(false) =>
        true
      case None =>
        warning("Interpreting None (timeout) as evidence for invalidity.")
        false
    }
  }
  
  override def checkValidityNoMod(expression: Expr) = {
    solver.push
    solver.assertCnstr(Not(expression))   
    val solverCheckResult = solver.check
    fine("Solver said " + solverCheckResult + " for " + expression)
    solver.pop()    
    solverCheckResult match {
      case Some(true) =>
        fine("And the model is " + solver.getModel)
        false
      case Some(false) =>
        true
      case None =>
        warning("Interpreting None (timeout) as evidence for invalidity.")
        false
    }
  }
  
  override def checkSatisfiabilityNoMod(expression: Expr) = {
    solver.push
    solver.assertCnstr(expression)   
    val solverCheckResult = solver.check
    fine("Solver said " + solverCheckResult + " for " + expression)
    solver.pop()    
    solverCheckResult match {
      case Some(true) =>
        true
      case Some(false) =>
        false
      case None =>
        false
    }
  }
  
}