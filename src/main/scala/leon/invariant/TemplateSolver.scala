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
import scala.concurrent._
import scala.concurrent.duration._
import ExecutionContext.Implicits.global
import leon.purescala.ScalaPrinter

abstract class TemplateSolver (ctx: InferenceContext, val rootFun : FunDef,
    ctrTracker : ConstraintTracker, val tempFactory: TemplateFactory) {   
  
  protected val reporter = ctx.reporter  
  //protected val cg = CallGraphUtil.constructCallGraph(program)
  
  //some constants
  protected val fls = BooleanLiteral(false)
  protected val tru = BooleanLiteral(true)    
  //protected val zero = IntLiteral(0)   
    
  private val dumpVC = false
  private val dumpVCasSMTLIB = false  
      
  /**
   * Completes a model by adding mapping to new template variables
   */
  def completeModel(model: Map[Identifier, Expr], tempIds: Set[Identifier]): Map[Identifier, Expr] = {
    tempIds.map((id) => {
      if (!model.contains(id)) {        
        (id, simplestValue(id.getType))
      } else (id, model(id))
    }).toMap
  }

    /**
   * Computes the invariant for all the procedures given a mapping for the
   * template variables.
   * (Undone) If the mapping does not have a value for an id, then the id is bound to the simplest value
   */
  def getAllInvariants(model: Map[Identifier, Expr]): Map[FunDef, Expr] = {
    val templates = ctrTracker.getFuncs.foldLeft(Seq[(FunDef, Expr)]())((acc, fd) => {

      val tempOption = tempFactory.getTemplate(fd)
      if (!tempOption.isDefined) acc
      else acc :+ (fd, tempOption.get)      
    })
    TemplateInstantiator.getAllInvariants(model, templates.toMap)
  }
  
  protected def getVCForFun(fd: FunDef) : Expr = {
    ctrTracker.getVC(fd).toExpr
  }
   
  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */  
  def solveTemplates(): (Option[Map[FunDef, Expr]], Option[Set[Call]]) = {
    
    //traverse each of the functions and collect the VCs
    val funcs = ctrTracker.getFuncs        
    val funcExprs = funcs.map((fd) => {      
      val vc = getVCForFun(fd)
      
      if (this.dumpVC) {
        //val simpForm = simplifyArithmetic(vc)
        val vcstr = vc.toString
        println("Func: " + fd.id + " VC: " + vcstr)
        val filename = "vc-" + FileCountGUID.getID        
        val wr = new PrintWriter(new File(filename + ".txt"))
        //ExpressionTransformer.PrintWithIndentation(wr, vcstr)
        wr.println(vcstr)
        wr.flush()
        wr.close()
        if (dumpVCasSMTLIB) {
          Util.toZ3SMTLIB(vc, filename + ".smt2", "QF_LIA", ctx.leonContext, ctx.program)
        }        
        println("Printed VC of " + fd.id + " to file: " + filename)
      }
                
      if (ctx.dumpStats) {                
        Stats.updateCounterStats(Util.atomNum(vc), "VC-size", "VC-refinement")        
        Stats.updateCounterStats(Util.numUIFADT(vc), "UIF+ADT", "VC-refinement")
      }            
      (fd -> vc)      
    }).toMap  
    
    //Assign some values for the template variables at random (actually use the simplest value for the type)
    val tempIds = funcs.foldLeft(Set[Identifier]())((acc, fd) => {
      val tempOption = tempFactory.getTemplate(fd)
      if (!tempOption.isDefined) acc
      else acc ++ variablesOf(tempOption.get).filter(TemplateIdFactory.IsTemplateIdentifier _)      
    })
    
    Stats.updateCounterStats(tempIds.size, "TemplateIds", "VC-refinement")       
       
    val solution = solve(tempIds, funcExprs)        
    solution
    //uncomment the following if you want to skip solving but are find with any arbitrary choice
    //Some(getAllInvariants(simplestModel))
  }
  
  def solve(tempIds : Set[Identifier], funcVCs : Map[FunDef,Expr]) : (Option[Map[FunDef,Expr]], Option[Set[Call]])
}

//class ParallelTemplateSolver(
//    context : LeonContext, 
//    program : Program,
//    ctrTracker : ConstraintTracker, 
//    tempFactory: TemplateFactory,    
//    timeout: Int) extends TemplateSolver(context, program, ctrTracker, tempFactory, timeout) {
//  
//  override def solveTemplates() : Option[Map[FunDef, Expr]] = {     
//    val tsol1 = new NLTemplateSolver(context, program, ctrTracker, tempFactory, timeout)
//    //TODO: change this later
//    //fixing a timeout of 100 seconds
//    val tsol2 = new CegisSolverIncr(context, program, ctrTracker, tempFactory, 100)
//    
//    val parFuture = Future.firstCompletedOf(Seq(future {tsol1.solveTemplates()}, future {tsol2.solveTemplates()}))    
//    Await.result(parFuture, Duration.Inf)
//  }
//  
//  override def solve(tempIds : Set[Identifier], funcVCs : Map[FunDef,Expr]) : Option[Map[FunDef,Expr]] = {
//    throw IllegalStateException("This is not supposed to be called")
//  }
//}