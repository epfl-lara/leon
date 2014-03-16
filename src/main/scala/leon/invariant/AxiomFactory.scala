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
import leon.solvers.SimpleSolverAPI
import leon.solvers.z3.UIFZ3Solver
import leon.invariant._
import leon.purescala.UndirectedGraph
import scala.util.control.Breaks._
import leon.solvers._
import scala.concurrent._
import scala.concurrent.duration._
import ExecutionContext.Implicits.global
import leon.purescala.ScalaPrinter
import leon.plugin.NonlinearityEliminationPhase

class AxiomFactory(ctx : LeonContext, program : Program) {                       
  
  //Add more axioms here, if necessary
  var commuCalls = Set[Call]()
  def hasUnaryAxiom(call: Call) : Boolean = {
    //important: here we need to avoid applying commutativity on the calls produced by axioms instantiation
    (FunctionInfoFactory.isCommutative(call.fi.funDef) && !commuCalls.contains(call)) 
  }
  
  def hasBinaryAxiom(call: Call) : Boolean = {
	FunctionInfoFactory.isMonotonic(call.fi.funDef)   
  }
  
  def unaryAxiom(call: Call) : Expr = {
    val callee = call.fi.funDef
    if(FunctionInfoFactory.isCommutative(callee)) {
      //note: commutativity is defined only for binary operations
      val Seq(a1, a2) = call.fi.args
      val newret = TVarFactory.createTemp("cm").toVariable
      val newfi = FunctionInvocation(callee,Seq(a2,a1))
      val newcall = Equals(newret,newfi)
      
      //note: calls added by this axiom cannot be again considered by this axiom
      commuCalls += Call(newret, newfi)
      
      And(newcall, Equals(newret, call.retexpr))
    } else 
      throw IllegalStateException("Call does not have unary axiom: "+call)
  }
  
  def binaryAxiom(call1: Call, call2: Call) : Expr = {    
    
    if(call1.fi.funDef.id != call2.fi.funDef.id) 
      throw IllegalStateException("Instantiating binary axiom on calls to different functions: "+call1+","+call2)
    
    val callee = call1.fi.funDef
    if(FunctionInfoFactory.isMonotonic(callee)) {
      monotonizeCalls(call1,call2)      
    } else 
      throw IllegalStateException("Call does not have binary axiom: "+call1)
  }
  
  def monotonizeCalls(call1: Call, call2: Call): Expr = {    
    val ant = (call1.fi.args zip call2.fi.args).foldLeft(Seq[Expr]())((acc, pair) => {
      val lesse = LessEquals(pair._1, pair._2)
      lesse +: acc
    })
    val conseq = LessEquals(call1.retexpr, call2.retexpr)
    Implies(And(ant), conseq)    
  }
   
  //TODO: add distributivity axiom
}
