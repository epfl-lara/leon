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

class Verifier(solver: IncrementalSolver, p: Problem, funDef: FunDef, synthInfo: SynthesisInfo)
	extends HasLogger {
    
  import SynthesisInfo.Action._
  
  def analyzeProgram = {
    synthInfo.start(Verification)

    // create an expression to verify
    val theExpr = generateVerificationCondition(funDef.getBody)
     
    solver.push
    val valid = checkValidity(theExpr)
    val map = solver.getModel
    solver.pop()

    // measure time
    synthInfo.end
    fine("Analysis took of theExpr: " + synthInfo.last)
    (valid, map)
  }

  def generateVerificationCondition(body: Expr) = {
        
    // replace recursive calls with fresh variables
    case class Replacement(id: Identifier, exprReplaced: FunctionInvocation) {
      def getMapping: Map[Expr, Expr] = {
        val funDef = exprReplaced.funDef
        val pairList = (ResultVariable(), id.toVariable) ::
        	(funDef.args.map(_.toVariable).toList zip exprReplaced.args)
      	pairList.toMap
      }
    }
    
    var isThereARecursiveCall = false
    var replacements = List[Replacement]() 
    
    // traverse the expression and check for recursive calls
    def replaceRecursiveCalls(expr: Expr) = expr match {
      case funInv@FunctionInvocation(`funDef`, args) => {
        isThereARecursiveCall = true
        val inductId = FreshIdentifier("induct", true).setType(funDef.returnType)
        replacements :+= Replacement(inductId, funInv)
        Some(inductId.toVariable)
      }
      case _ => None
    }
    
    val newBody = searchAndReplace(replaceRecursiveCalls)(body)
       
    val resFresh = FreshIdentifier("result", true).setType(newBody.getType)
    val bodyAndPost = 		    
	    Let(
    		resFresh, newBody,
    		replace(Map(ResultVariable() -> resFresh.toVariable), matchToIfThenElse(funDef.getPostcondition))
  		)	

		val precondition = if( isThereARecursiveCall ) {
		  And( funDef.getPrecondition :: replacements.map( r => replace(r.getMapping, funDef.getPostcondition)) )
		} else
		  funDef.getPrecondition
  		
    val withPrec = 
      Implies(matchToIfThenElse(precondition), bodyAndPost)

    fine("Generated verification condition: " + withPrec)
    withPrec
  }
  
  def checkValidity(expression: Expr) = {
    solver.assertCnstr(Not(expression))   
    val solverCheckResult = solver.check
    fine("Solver said " + solverCheckResult + " for " + expression)
    solverCheckResult match {
      case Some(true) =>
        false
      case Some(false) =>
        true
      case None =>
        warning("Interpreting None (timeout) as evidence for validity.")
        true
    }
  }
  
  def checkValidityNoMod(expression: Expr) = {
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
        warning("Interpreting None (timeout) as evidence for validity.")
        true
    }
  }
  
  def checkSatisfiabilityNoMod(expression: Expr) = {
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
  
//  private def checkSatisfiability = {
//    
//  }
  
}