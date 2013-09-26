package leon
package synthesis
package condabd
package verification

import solvers._
import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import _root_.insynth.util.logging._

class Verifier(solverf: SolverFactory[Solver], p: Problem, synthInfo: SynthesisInfo = new SynthesisInfo)
	extends AbstractVerifier(solverf, p, synthInfo) with HasLogger {
    
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
