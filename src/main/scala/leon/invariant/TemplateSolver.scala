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
import scala.concurrent._
import scala.concurrent.duration._
import ExecutionContext.Implicits.global
import leon.purescala.ScalaPrinter
import leon.plugin.NonlinearityEliminationPhase

abstract class TemplateSolver (
    context : LeonContext, 
    program : Program,
    val rootFun : FunDef,
    ctrTracker : ConstraintTracker, 
    val tempFactory: TemplateFactory,    
    timeout: Int) {   
  
  protected val reporter = context.reporter  
  protected val cg = CallGraphUtil.constructCallGraph(program)
  
  //some constants
  protected val fls = BooleanLiteral(false)
  protected val tru = BooleanLiteral(true)    
  protected val zero = IntLiteral(0)   
  
  //this is populated lazily by instantiateAxioms
  protected var callsWithAxioms = Set[Expr]()
  
  //disable axiom instantiation
  protected val disableAxioms = false
  
  //for debugging
  protected val debugInstrumentation = false
  private val debugAxiomInstantiation = false
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
   
  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */  
  def solveTemplates(): (Option[Map[FunDef, Expr]], Option[Set[Call]]) = {
           
    Stats.updateCounter(1, "VC-refinement")
    
    //traverse each of the functions and collect the VCs
    val funcs = ctrTracker.getFuncs        
    val funcExprs = funcs.map((fd) => {
      val (btree, ptree) = ctrTracker.getVC(fd)
      val bexpr = TreeUtil.toExpr(btree)
      val pexpr = TreeUtil.toExpr(ptree)
      
      val (rg, formula) = instrumentWithGuards(And(bexpr, pexpr))
      rootGuards += (fd -> rg)
      
      if(this.debugAxiomInstantiation) {
        println("Func: " + fd.id + " VC before instantiation: " + formula)
        val filename = "plainVC-" + FileCountGUID.getID        
        val wr = new PrintWriter(new File(filename + ".txt"))
        val printableExpr = simplifyArithmetic(formula) 
            //variablesOf(formula).filterNot(TVarFactory.isTemporary _))
        ExpressionTransformer.PrintWithIndentation(wr, printableExpr)        
        wr.flush()
        wr.close()
        println("Printed plain VC of " + fd.id + " to file: " + filename)
      }
                 
      //apply (instantiate) the axioms of functions in the verification condition
      val formulaWithAxioms = if(this.disableAxioms) formula else instantiateAxioms(formula)

      if (this.debugAxiomInstantiation || this.dumpVC) {
        println("Func: " + fd.id + " VC: " + formulaWithAxioms)
        val filename = "vc-" + FileCountGUID.getID        
        val wr = new PrintWriter(new File(filename + ".txt"))
        ExpressionTransformer.PrintWithIndentation(wr, simplifyArithmetic(formulaWithAxioms))        
        wr.flush()
        wr.close()

        if (dumpVCasSMTLIB) {
          InvariantUtil.toZ3SMTLIB(formulaWithAxioms, filename + ".smt2", "QF_LIA", context, program)
        }        
        println("Printed VC of " + fd.id + " to file: " + filename)
      }
                
      if (InferInvariantsPhase.dumpStats) {
        val plainVCsize = InvariantUtil.atomNum(formula)
        val vcsize = InvariantUtil.atomNum(formulaWithAxioms)        
        Stats.updateCounterStats(vcsize, "VC-size", "VC-refinement")
        Stats.updateCounterStats(vcsize - plainVCsize, "AxiomBlowup", "VC-refinement")
        Stats.updateCounterStats(InvariantUtil.numUIFADT(formula), "UIF+ADT", "VC-refinement")
      }            
      
      //instrument the formula with booleans baurgs      
      (fd -> formulaWithAxioms)      
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
  
  def monotonizeCalls(call1: Expr, call2: Expr): (Seq[Expr], Expr) = {
    val BinaryOperator(r1 @ Variable(_), fi1 @ FunctionInvocation(fd1, args1), _) = call1
    val BinaryOperator(r2 @ Variable(_), fi2 @ FunctionInvocation(fd2, args2), _) = call2
    
    if(fd1.id != fd2.id) 
      throw IllegalStateException("Monotonizing calls to different functions: "+call1+","+call2)
   
    val ant = (args1 zip args2).foldLeft(Seq[Expr]())((acc, pair) => {
      val lesse = LessEquals(pair._1, pair._2)
      lesse +: acc
    })
    val conseq = LessEquals(r1, r2)
    (ant, conseq)
  }
  
  //a mapping from axioms keys (for now pairs of calls) to the guards
  protected var axiomRoots = Map[(Expr,Expr),Variable]()
  
  def instantiateAxioms(formula: Expr): Expr = {

    val debugSolver = if (this.debugAxiomInstantiation) {
      val sol = new UIFZ3Solver(context, program)
      sol.assertCnstr(formula)
      Some(sol)
    } else None    
    
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
        //important: check if the two calls refer to the same function
        val BinaryOperator(_, FunctionInvocation(fd1, _), _) = call1
        val BinaryOperator(_, FunctionInvocation(fd2, _), _) = call2               
        if((fd1.id == fd2.id) && (call1 != call2))
          product = (call1, call2) +: product
      })
    })    
    val axiomInstances = product.foldLeft(Seq[Expr]())((acc, pair) => {      
      val (ants, conseq) = monotonizeCalls(pair._1, pair._2)
      
      import ExpressionTransformer._
      val nnfAxiom = pullAndOrs(TransformNot(Implies(And(ants), conseq)))
      
      val (axroot, axiomCtr) = instrumentWithGuards(nnfAxiom)
      axiomRoots += (pair -> axroot)
      
      acc :+ axiomCtr
    })
    
    //for debugging
    reporter.info("Number of axiom instances: "+2 * axiomCallsInFormula.size * axiomCallsInFormula.size)
    //println("Axioms: "+axiomInstances)
   
    if(this.debugAxiomInstantiation) {
      println("Instantiated Axioms")
      axiomInstances.foreach((ainst) => {        
        println(ainst)
        debugSolver.get.assertCnstr(ainst)
        val res = debugSolver.get.check
        res match {
          case Some(false) => 
            println("adding axiom made formula unsat!!")            
          case _ => ;
        }
      })
      debugSolver.get.free
    }
    val axiomInst = And(axiomInstances)
    And(formula, axiomInst)
  }

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