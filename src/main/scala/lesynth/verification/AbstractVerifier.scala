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

abstract class AbstractVerifier(solver: IncrementalSolver, p: Problem,
  synthInfo: SynthesisInfo)
	extends HasLogger {
    
  import SynthesisInfo.Action._
  
  def analyzeFunction(funDef: FunDef) = {
    synthInfo.start(Verification)

    // create an expression to verify
    val theExpr = generateInductiveVerificationCondition(funDef, funDef.getBody)
     
    solver.push
    val valid = checkValidity(theExpr)
    val map = solver.getModel
    solver.pop()

    // measure time
    synthInfo.end
    fine("Analysis of " + theExpr + ",took :" + synthInfo.last)
    (valid, map)
  }
  
  def analyzeFunction(funDef: FunDef, body: Expr) = {
    synthInfo.start(Verification)

    // create an expression to verify
    val theExpr = generateInductiveVerificationCondition(funDef, body)
     
    solver.push
    val valid = checkValidity(theExpr)
    val map = solver.getModel
    solver.pop()

    // measure time
    synthInfo.end
    fine("Analysis of " + theExpr + ",took :" + synthInfo.last)
    (valid, map)
  }

  protected def generateInductiveVerificationCondition(funDef: FunDef, body: Expr) = {
        
    // replace recursive calls with fresh variables
    case class Replacement(id: Identifier, exprReplaced: FunctionInvocation) {
      def getMapping: Map[Expr, Expr] = {
        val funDef = exprReplaced.funDef
        val pairList = (ResultVariable(), id.toVariable) ::
        	(funDef.args.map(_.toVariable).toList zip exprReplaced.args)
      	pairList.toMap
      }
    }
    
    // traverse the expression and check (and replace) recursive calls
    var isThereARecursiveCall = false
    var replacements = List[Replacement]() 
    
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
       
    // build the verification condition
    val resFresh = FreshIdentifier("result", true).setType(newBody.getType)
    val bodyAndPost = 		    
	    Let(
    		resFresh, newBody,
    		replace(Map(ResultVariable() -> resFresh.toVariable), matchToIfThenElse(p.pc))
  		)	

		val precondition = if( isThereARecursiveCall ) {
		  And( p.phi :: replacements.map( r => replace(r.getMapping, p.pc)) )
		} else
		  p.phi
  		
    val withPrec = 
      Implies(matchToIfThenElse(precondition), bodyAndPost)

    fine("Generated verification condition: " + withPrec)
    withPrec
  }
  
  def checkValidity(expression: Expr): Boolean
  
  def checkValidityNoMod(expression: Expr): Boolean
  
  def checkSatisfiabilityNoMod(expression: Expr): Boolean
  
}