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
import leon.verification.ExtendedVC
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.solvers.SimpleSolverAPI
import leon.solvers.z3.UIFZ3Solver
import leon.invariant._
import leon.purescala.UndirectedGraph
import scala.util.control.Breaks._
import leon.solvers._

abstract class TemplateSolver (
    context : LeonContext, 
    program : Program,
    ctrTracker : ConstraintTracker, 
    tempFactory: TemplateFactory,    
    timeout: Int) {   
  
  protected val reporter = context.reporter  
  protected val cg = CallGraphUtil.constructCallGraph(program)
  
  //some constants
  protected val fls = BooleanLiteral(false)
  protected val tru = BooleanLiteral(true)    
  protected val zero = IntLiteral(0)
  
  //this is populated lazily by instantiateAxioms
  protected var callsWithAxioms = Set[Expr]()
      
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

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */  
  def solveTemplates(): Option[Map[FunDef, Expr]] = {
        
    //for stats
    Stats.outerIterations += 1
    
    //traverse each of the functions and collect the VCs
    val funcs = ctrTracker.getFuncs
    val funcExprs = funcs.map((fd) => {
      val (btree, ptree) = ctrTracker.getVC(fd)
      val bexpr = TreeUtil.toExpr(btree)
      val pexpr = TreeUtil.toExpr(ptree)
      
      val formula = And(bexpr, pexpr)
      
      //apply (instantiate) the axioms of functions in the verification condition
      val formulaWithAxioms = instantiateAxioms(formula)
      
      //stats      
      if (InferInvariantsPhase.dumpStats) {
        val plainVCsize = InvariantUtil.atomNum(formula)
        val vcsize = InvariantUtil.atomNum(formulaWithAxioms)
        val (cum, max) = Stats.cumMax(Stats.cumVCsize, Stats.maxVCsize, vcsize)
        Stats.cumVCsize = cum; Stats.maxVCsize = max

        val (cum2, max2) = Stats.cumMax(Stats.cumUIFADTs, Stats.maxUIFADTs, InvariantUtil.numUIFADT(formula))
        Stats.cumUIFADTs = cum2; Stats.maxUIFADTs = max2

        val (cum1, max1) = Stats.cumMax(Stats.cumLemmaApps, Stats.maxLemmaApps, vcsize - plainVCsize)
        Stats.cumLemmaApps = cum1; Stats.maxLemmaApps = max1
      }
            
      
      (fd -> formulaWithAxioms)
    }).toMap  
    
    //Assign some values for the template variables at random (actually use the simplest value for the type)
    val tempIds = funcs.foldLeft(Set[Identifier]())((acc, fd) => {
      val tempOption = tempFactory.getTemplate(fd)
      if (!tempOption.isDefined) acc
      else acc ++ variablesOf(tempOption.get).filter(TemplateIdFactory.IsTemplateIdentifier _)      
    })

    //stats
    if (InferInvariantsPhase.dumpStats) {
      val (cum3, max3) = Stats.cumMax(Stats.cumTempVars, Stats.maxTempVars, tempIds.size)
      Stats.cumTempVars = cum3; Stats.maxTempVars = max3
    }      
       
    val solution = solve(tempIds, funcExprs)        
    solution
    //uncomment the following if you want to skip solving but are find with any arbitrary choice
    //Some(getAllInvariants(simplestModel))
  }
  
  def solve(tempIds : Set[Identifier], funcVCs : Map[FunDef,Expr]) : Option[Map[FunDef,Expr]]

  def monotonizeCalls(call1: Expr, call2: Expr): (Seq[Expr], Expr) = {
    val BinaryOperator(r1 @ Variable(_), fi1 @ FunctionInvocation(fd1, args1), _) = call1
    val BinaryOperator(r2 @ Variable(_), fi2 @ FunctionInvocation(fd2, args2), _) = call2
    //here implicitly assumed that fd1 == fd2 and fd1 has a monotonicity axiom, 
    //TODO: in general we need to assert this here
    val ant = (args1 zip args2).foldLeft(Seq[Expr]())((acc, pair) => {
      val lesse = LessEquals(pair._1, pair._2)
      lesse +: acc
    })
    val conseq = LessEquals(r1, r2)
    (ant, conseq)
  }
  
  def instantiateAxioms(formula: Expr): Expr = {    
    var axiomCallsInFormula = Set[Expr]()
    
    //collect all calls with axioms    
    simplePostTransform((e: Expr) => e match {
      case call @ _ if (InvariantUtil.isCallExpr(e)) => {
        val BinaryOperator(_, FunctionInvocation(fd, _), _) = call
        if (FunctionInfoFactory.isMonotonic(fd)) {
          callsWithAxioms += call
          axiomCallsInFormula += call
        }
          
        call
      }
      case _ => e
    })(formula)    
        
    var product = Seq[(Expr,Expr)]() 
    axiomCallsInFormula.foreach((call1) =>{
      axiomCallsInFormula.foreach((call2) => {
        if(call1 != call2)
          product = (call1, call2) +: product
      })
    })    
    val axiomInstances = product.foldLeft(Seq[Expr]())((acc, pair) => {      
      val (ants, conseq) = monotonizeCalls(pair._1, pair._2)
      acc :+ Implies(And(ants), conseq)
    })
    
    //for debugging
    reporter.info("Number of axiom instances: "+2 * axiomCallsInFormula.size * axiomCallsInFormula.size)
    //println("Axioms: "+axiomInstances)
    
    val axiomInst = ExpressionTransformer.TransformNot(And(axiomInstances))
    And(formula, axiomInst)
  }
}
