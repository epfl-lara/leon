package leon
package invariant

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TrivialSolver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
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
import leon.verification.ExtendedVC
import leon.verification.Tactic
import leon.verification.VerificationReport
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }

/**
   * An enumeration based template generator.
   * Enumerates all numerical terms in some order (this enumeration is incomplete for termination).
   * TODO: Feature: 
   * (a) allow template functions and functions with template variables ?
   * 
   * The following function may potentially have complexity O(n^i) where 'n' is the number of functions
   * and 'i' is the increment step
   * TODO: optimize the running and also reduce the size of the input templates
   * 
   * For now this is incomplete 
   */
class TemplateEnumerator(fd: FunDef, prog: Program) extends TemplateGenerator {
	private val MAX_INCREMENTS = 2  
	private var currTemp : Expr = null
	private var incrStep : Int = 0	
	private var typeTermMap = Map[TypeTree,MutableSet[Expr]]()
	private var ttCurrent = Map[TypeTree,MutableSet[Expr]]()
	
	private val fds = prog.definedFunctions
	
	def getNextTemplate() : Expr = {
	  if(incrStep == MAX_INCREMENTS) currTemp
	  else {
	    
	   incrStep += 1	   
	   if(currTemp == null) {
        //initialize
        //add all the arguments and results of fd to 'typeTermMap'
        fd.args.foreach((vardecl) => {
          val tpe = vardecl.tpe
          val v = vardecl.id.toVariable
          if (ttCurrent.contains(tpe)) {
            ttCurrent(tpe).add(v)
          } else {
            ttCurrent += (tpe -> MutableSet(v))
          }
        })
        if (ttCurrent.contains(fd.returnType)) {
          ttCurrent(fd.returnType).add(ResultVariable())
        } else {
          ttCurrent += (fd.returnType -> MutableSet(ResultVariable()))
        }   
        typeTermMap = ttCurrent	     
        
        //also 'assignCurrTemp' to a template variable
        currTemp = TemplateFactory.freshTemplateVar()        
	   }
	   
	   //apply the user-defined functions to the compatible terms in typeTermMap        
        val newTerms = Map[TypeTree,MutableSet[Expr]]()
         
        fds.foreach((fun) => {
          if(!fun.args.filter((vardecl) => !ttCurrent.contains(vardecl.tpe)).isEmpty) {
            //every argument has at least one satisfying assignment so compute all the combinations
        	val newcalls = generateFunctionCalls(fun)
        	if(newTerms.contains(fun.returnType)) {
        	  newTerms(fun.returnType) ++= newcalls
        	}        	        	
          }          
        })
        
        //add all the newly generated expression to the typeTermMap
	    ttCurrent = newTerms
	    typeTermMap ++= newTerms
	    
	    //return all the integer valued terms of newTerms
	    val intTerms = if(newTerms.contains(Int32Type)) newTerms(Int32Type)
	    			   else Set()
	    //create a linear combination of intTerms
	    val newTemp = intTerms.foldLeft(null : Expr)((acc, t)=> {
	    					val summand = Times(TemplateFactory.freshTemplateVar(),t)	    					
	    					if(acc == null) summand
	    					else 
	    						Plus(summand, acc)
	    			   })
        //add newTemp to currTemp
	    currTemp = Plus(newTemp, currTemp)
	    currTemp
	  }	    
	}
	
	/**
	 * Generate a set of function calls of fun using the terms in ttCurrent
	 */
	def generateFunctionCalls(fun: FunDef) : Set[Expr] = {
	  /**
	   * To be called with argIndex of zero and an empty argList 
	   */
	  def genFunctionCallsRecur(argIndex : Int, argList : Seq[Expr]) : Set[Expr] ={
	    if(argIndex == fun.args.size) {	    	
	      //create a call using argList
	      Set(FunctionInvocation(fun,argList))
	    } else {
	    	val arg = fun.args(argIndex)
	    	val tpe = arg.tpe
	    	ttCurrent(tpe).foldLeft(Set[Expr]())((acc, term) => acc ++ genFunctionCallsRecur(argIndex + 1, argList :+ term))  
	    }	    	    
	  }
	  
	  genFunctionCallsRecur(0, Seq())
	}
	
}