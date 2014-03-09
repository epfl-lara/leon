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

class AxiomInstantiator(ctx : LeonContext, program : Program, ctrTracker : ConstraintTracker) {   
    
  //some constants
  protected val fls = BooleanLiteral(false)
  protected val tru = BooleanLiteral(true)    
  protected val zero = IntLiteral(0)     
    
  protected val debugAxiomInstantiation = false
    
  //a mapping from functions to the index of the vcList that has been processed
  protected var exploredVCIndex = Map[FunDef,Int]()
  //calls with axioms so far been encountered
  protected var callsWithAxioms = Set[Expr]() 
  //a mapping from axioms keys (for now pairs of calls) to the guards
  protected var axiomRoots = Map[(Expr,Expr),Variable]()
   
  def instantiate() = {
                 
    val funcs = ctrTracker.getFuncs        
    funcs.foreach((fd) => {
      val vcList = ctrTracker.getVC(fd)      
      //the index of the vc list that is processed by the instantiator
      val prevIndex = this.exploredVCIndex.getOrElse(fd, {
        exploredVCIndex += (fd -> 0)
        0
      })        
      val newParts = vcList.slice(prevIndex, vcList.size)      
      
      if(this.debugAxiomInstantiation) {
        val simpForm = simplifyArithmetic(And(newParts))
        println("Instantianting: " + simpForm)
        val filename = "instFormula-" + FileCountGUID.getID        
        val wr = new PrintWriter(new File(filename + ".txt"))
        //val printableExpr = variablesOf(formula).filterNot(TVarFactory.isTemporary _))
        ExpressionTransformer.PrintWithIndentation(wr, simpForm)        
        wr.flush()
        wr.close()
        println("Printed instFormula to file: " + filename)
      }
      
      val newInstantiations = instantiateAxioms(And(vcList), And(newParts))
      //update previous index
      exploredVCIndex -= fd
      exploredVCIndex += (fd -> vcList.size)
      //add new axioms to the vc
      ctrTracker.conjoinWithVC(fd, newInstantiations)

      if (this.debugAxiomInstantiation) {
        val simpForm = simplifyArithmetic(newInstantiations)
        println("Axioms added: " + simpForm)
        val filename = "axiomInst-" + FileCountGUID.getID        
        val wr = new PrintWriter(new File(filename + ".txt"))
        ExpressionTransformer.PrintWithIndentation(wr, simpForm)        
        wr.flush()
        wr.close()        
        println("Printed axioms instantiated to file: " + filename)
      }                
      Stats.updateCounterStats(InvariantUtil.atomNum(newInstantiations), "AxiomBlowup", "VC-refinement")              
    })    
  }
   
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
   
  def instantiateAxioms(formula: Expr, newPart: Expr): Expr = {

    val debugSolver = if (this.debugAxiomInstantiation) {
      val sol = new UIFZ3Solver(ctx, program)
      sol.assertCnstr(formula)
      Some(sol)
    } else None    
        
    val newCalls = InvariantUtil.getCallExprs(newPart).filter(_ match {
      case BinaryOperator(_, FunctionInvocation(fd, _), _) => {
        //for now handling only monotonicity axiom
         FunctionInfoFactory.isMonotonic(fd)
      }
    })

    def isInstatiable(call1: Expr, call2: Expr): Boolean = {
      //important: check if the two calls refer to the same function
      val BinaryOperator(_, FunctionInvocation(fd1, _), _) = call1
      val BinaryOperator(_, FunctionInvocation(fd2, _), _) = call2
      (fd1.id == fd2.id) && (call1 != call2)
    }
        
    def cross(a : Set[Expr], b: Set[Expr]) : Set[(Expr,Expr)] = {
      (for (x<-a; y<-b) yield (x,y)).filter(pair => isInstatiable(pair._1,pair._2))
    } 
      
    val product = cross(newCalls,callsWithAxioms).flatMap(p => Seq((p._1,p._2),(p._2,p._1))) ++
      cross(newCalls,newCalls).map(p => (p._1,p._2))
    
    //update calls with axioms
    callsWithAxioms ++= newCalls
            
    val axiomInstances = product.foldLeft(Seq[Expr]())((acc, pair) => {      
      val (ants, conseq) = monotonizeCalls(pair._1, pair._2)
     
      import ExpressionTransformer._
      val nnfAxiom = pullAndOrs(TransformNot(Implies(And(ants), conseq)))
      
      val (axroot, axiomInst) = ctrTracker.instrumentWithGuards(nnfAxiom)
      axiomRoots += (pair -> axroot)
      
      acc :+ axiomInst
    })
    
    //for debugging
    ctx.reporter.info("Number of axiom instances: "+axiomInstances.size)
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
    And(axiomInstances)    
  }

}