package leon
package invariant

import z3.scala._
import purescala._
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
import leon.verification.ExtendedVC
import leon.verification.Tactic
import leon.verification.VerificationReport
 
class ConstraintTracker(context:LeonContext, program: Program, rootFun : FunDef, temFactory: TemplateFactory) {
  
  //for debugging  
  protected val disableAxioms = false
    
  //a mapping from functions to its VCs represented as a CNF formula
  protected var funcVCs = Map[FunDef,Formula]()
  
  val vcRefiner = new RefinementEngine(context, program, this, temFactory)
  val axiomInstantiator = new AxiomInstantiator(context, program, this)
  
  def getFuncs : Seq[FunDef] = funcVCs.keys.toSeq
  def hasVC(fdef: FunDef) = funcVCs.contains(fdef)  
  def getVC(fd: FunDef) : Formula = funcVCs(fd)
  
  def addVC(fd: FunDef, vc: Expr) = {       
    funcVCs += (fd -> new Formula(vc))     
  }
  
  def initialize = {
    //initialize unrolling
    vcRefiner.initialize
    //add axioms 
    if(!disableAxioms) {
      this.axiomInstantiator.instantiate
    }
  }

  def refineVCs(toUnrollCalls: Option[Set[Call]]) : Set[Call]  = {
    val unrolledCalls = vcRefiner.refineAbstraction(toUnrollCalls)    
    //add axioms
    if(!disableAxioms) {
      this.axiomInstantiator.instantiate
    }
    unrolledCalls
  }  
}