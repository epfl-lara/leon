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

abstract class AbstractVerifier(solverf: SolverFactory[Solver], p: Problem, synthInfo: SynthesisInfo)
	extends HasLogger {
    
  val solver = solverf.getNewSolver

  import SynthesisInfo.Action._
  
  def analyzeFunction(funDef: FunDef) = {
    synthInfo.start(Verification)
    fine("Analyzing function: " + funDef)

    // create an expression to verify
    val theExpr = generateInductiveVerificationCondition(funDef, funDef.body.get)
     
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
        val pairList = (Variable(funDef.postcondition.get._1), id.toVariable) ::
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
    val (id, post) = funDef.postcondition.get
    val bodyAndPost =
	    Let(
    		resFresh, newBody,
    		replace(Map(Variable(id) -> resFresh.toVariable), matchToIfThenElse(post))
  		)	

		val precondition = if( isThereARecursiveCall ) {
		  And( funDef.precondition.get :: replacements.map( r => replace(r.getMapping, post)) )
		} else
		  funDef.precondition.get
//    val bodyAndPost = 		    
//	    Let(
//    		resFresh, newBody,
//    		replace(Map(p.xs.head.toVariable -> resFresh.toVariable), matchToIfThenElse(p.phi))
//  		)	
//
//		val precondition = if( isThereARecursiveCall ) {
//		  And( p.pc :: replacements.map( r => replace(r.getMapping, p.phi)) )
//		} else
//		  p.pc
  		
    val withPrec = 
      Implies(matchToIfThenElse(precondition), bodyAndPost)

    info("Generated verification condition: " + withPrec)
    withPrec
  }
  
  def checkValidity(expression: Expr): Boolean
  
  def checkValidityNoMod(expression: Expr): Boolean
  
  def checkSatisfiabilityNoMod(expression: Expr): Boolean
  
}
