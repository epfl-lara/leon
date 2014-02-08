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

class CegisSolver(context : LeonContext, 
    program : Program,
    rootFun : FunDef,
    ctrTracker : ConstraintTracker, 
    tempFactory: TemplateFactory,    
    timeout: Int,
    bound: Option[Int] = None) extends TemplateSolver(context, program, rootFun, ctrTracker, tempFactory, timeout) {
        
  override def solve(tempIds: Set[Identifier], funcVCs: Map[FunDef, Expr]): (Option[Map[FunDef, Expr]], Option[Set[Call]]) = {

    val initCtr = if (bound.isDefined) {
      //use a predefined bound on the template variables                 
      And(tempIds.map((id) => {
        val idvar = id.toVariable
        And(Implies(LessThan(idvar, zero), GreaterEquals(idvar, IntLiteral(-bound.get))),
          Implies(GreaterEquals(idvar, zero), LessEquals(idvar, IntLiteral(bound.get))))
      }).toSeq)
      
    } else tru
    
    val funcs = funcVCs.keys
    val formula = Or(funcs.map(funcVCs.apply _).toSeq)
    
    //using reals with bounds does not converge and also results in overflow
    val (res, _, model) = (new CegisCore(context, program, timeout, this)).solve(tempIds, formula, initCtr, solveAsInt = true)
    res match {
      case Some(true) => (Some(getAllInvariants(model)), None)
      case Some(false) => (None, None) //no solution exists 
      case _ => //timed out
        throw IllegalStateException("Timeout!!")
    }
  }  
}


class CegisCore(context : LeonContext, 
    program : Program,
    timeout: Int, cegisSolver: TemplateSolver) {
  
  val fls = BooleanLiteral(false)
  val tru = BooleanLiteral(true)
  val zero = IntLiteral(0)
  val timeoutMillis = timeout.toLong * 1000
  val dumpCandidateInvs = false
  
  /**
   * Finds a model for the template variables in the 'formula' so that 'formula' is falsified
   * subject to the constraints on the template variables given by the 'envCtrs'
   *
   * The parameter solveAsInt when set to true will convert the template constraints 
   * to integer constraints and solve. This should be enabled when bounds are used to constrain the variables   
   */
  def solve(tempIds: Set[Identifier], formula: Expr, initCtr: Expr, solveAsInt : Boolean, 
      initModel : Option[Map[Identifier, Expr]] = None)
  	: (Option[Boolean], Expr, Map[Identifier, Expr]) = {
    
    //start a timer
    val startTime = System.currentTimeMillis()
    
    //for some sanity checks
    var oldModels = Set[Expr]()
    def addModel(m: Map[Identifier, Expr]) = {
      val mexpr = InvariantUtil.modelToExpr(m)
      if (oldModels.contains(mexpr))
        throw IllegalStateException("repeating model !!:" + m)
      else oldModels += mexpr
    }

    //add the initial model    
    val simplestModel = if (initModel.isDefined) initModel.get else {
      tempIds.map((id) => (id -> simplestValue(id.toVariable))).toMap
    }
    addModel(simplestModel)
     
    
    //convert initCtr to a real-constraint
    val initRealCtr = ExpressionTransformer.convertIntLiteralToReal(initCtr)
    if(InvariantUtil.hasInts(initRealCtr)) 
      throw IllegalStateException("Initial constraints have integer terms: " + initRealCtr)

    def cegisRec(model: Map[Identifier, Expr], prevctr: Expr): (Option[Boolean], Expr, Map[Identifier, Expr]) = {
      
      val elapsedTime = (System.currentTimeMillis() - startTime)
      if (elapsedTime >= timeoutMillis - 100) {
        //if we have timed out return the present set of constrains and the current model we have
        (None, prevctr, model)
      } else {

        //println("elapsedTime: "+elapsedTime / 1000+" timeout: "+timeout)
        if (InferInvariantsPhase.dumpStats)
          Stats.cegisIterations += 1

        if (dumpCandidateInvs) {
          println("candidate Invariants")
          val candInvs = cegisSolver.getAllInvariants(model)
          candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))
        }
        val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable, elem._2)).toMap
        val instFormula = simplifyArithmetic(TemplateInstantiator.instantiate(formula, tempVarMap))

        //sanity checks
        val spuriousTempIds = variablesOf(instFormula).intersect(TemplateIdFactory.getTemplateIds)
        if (!spuriousTempIds.isEmpty)
          throw IllegalStateException("Found a template variable in instFormula: " + spuriousTempIds)              
        if (InvariantUtil.hasReals(instFormula))
          throw IllegalStateException("Reals in instFormula: " + instFormula)


        //println("solving instantiated vcs...")
        val t1 = System.currentTimeMillis()                
        val solver1 = new UIFZ3Solver(context, program)
        solver1.assertCnstr(instFormula)
        val res = solver1.check
        val t2 = System.currentTimeMillis()
        println("1: " + (if (res.isDefined) "solved" else "timedout") + "... in " + (t2 - t1) / 1000.0 + "s")

        res match {
          case Some(true) => {

            //instantiate vcs with newmodel
            /*val progVarMap: Map[Expr, Expr] = progModel.map((elem) => (elem._1.toVariable, elem._2)).toMap
          val tempctrs = replace(progVarMap, Not(formula))*/

            //simplify the tempctrs, evaluate every atom that does not involve a template variable
            //this should get rid of all functions
            val satctrs =
              simplePreTransform((e) => e match {
                //is 'e' free of template variables ? 
                case _ if (variablesOf(e).filter(TemplateIdFactory.IsTemplateIdentifier _).isEmpty) => {
                  //evaluate the term
                  val value = solver1.evalExpr(e)
                  if (value.isDefined) value.get
                  else throw IllegalStateException("Cannot evaluate expression: " + e)
                }
                case _ => e
              })(Not(formula))
            solver1.free()
            
            //sanity checks
            val spuriousProgIds = variablesOf(satctrs).filterNot(TemplateIdFactory.IsTemplateIdentifier _)
            if (!spuriousProgIds.isEmpty)
              throw IllegalStateException("Found a progam variable in tempctrs: " + spuriousProgIds)            
            
            val tempctrs = if(!solveAsInt) ExpressionTransformer.convertIntLiteralToReal(satctrs) else satctrs
            val newctr = And(tempctrs, prevctr)
            //println("Newctr: " +newctr)

            if (InferInvariantsPhase.dumpStats) {
              val (cum, max) = Stats.cumMax(Stats.cumTemplateCtrSize, Stats.maxTemplateCtrSize, InvariantUtil.atomNum(newctr))
              Stats.cumTemplateCtrSize = cum; Stats.maxTemplateCtrSize = max;
            }

            //println("solving template constraints...")
            val t3 = System.currentTimeMillis()
            val elapsedTime = (t3 - startTime)
            val solver2 = SimpleSolverAPI(new TimeoutSolverFactory(
              SolverFactory(() => new UIFZ3Solver(context, program)),
              timeoutMillis - elapsedTime))

            val (res1, newModel) = if (solveAsInt) {
              //convert templates to integers and solve. Finally, re-convert integer models for templates to real models
              val rti = new RealToInt()
              val (res1, intModel) = solver2.solveSAT(rti.mapRealToInt(And(newctr, initRealCtr)))
              (res1, rti.unmapModel(intModel))
            } else {
              
              /*if(InvariantUtil.hasInts(tempctrs)) 
            	throw IllegalStateException("Template constraints have integer terms: " + tempctrs)*/
              solver2.solveSAT(And(newctr, initRealCtr))
            } 
            
            val t4 = System.currentTimeMillis()
            println("2: " + (if (res1.isDefined) "solved" else "timed out") + "... in " + (t4 - t3) / 1000.0 + "s")

            if (res1.isDefined) {
              if (res1.get == false) {
                //there exists no solution for templates
                (Some(false), newctr, Map())

              } else {
                //this is for sanity check
                addModel(newModel)
                //generate more constraints
                cegisRec(newModel, newctr)
              }
            } else {
              //we have timed out 
              (None, prevctr, model)
            }
          }
          case Some(false) => {
            solver1.free()
            //found a model for disabling the formula
            (Some(true), prevctr, model)
          } case _ => {
            solver1.free()
            throw IllegalStateException("Cannot solve instFormula: "+instFormula)
          }
        }
      }
    }
    //note: initRealCtr is used inside 'cegisRec'
    cegisRec(simplestModel, tru)
  }
}

/**
 * TODO: Can we optimize timeout cases ?
 * That is, if we know we are going to timeout, we can return None immediately
 */
/*class CegisCoreIncr(context : LeonContext, 
    program : Program,
    timeout: Int,
    incrStep : Int = 5, 
    initBound : Int = 1) {
  
  val fls = BooleanLiteral(false)
  val tru = BooleanLiteral(true)
  val zero = IntLiteral(0)
  val timeoutMillis = timeout.toLong * 1000
  
  var currentCtr : Expr = tru
  var bound = initBound
  
  *//**
   * The following procedure can never prove unsat.
   * It can only be used to prove sat quickly.
   *//*
  def solveInSteps(tempIds: Set[Identifier], formula: Expr)
    : (Option[Boolean], Expr, Map[Identifier, Expr]) = {    
    
    //start with a bound of initial bound  and increase in steps given by incrStep    
    var timedout = false
    var solved = false  
    var currModel = Map[Identifier, Expr]()
    
    //start a timer
    val startTime = System.currentTimeMillis()
    
    while(!solved && !timedout) {
      
      val boundctr = And(tempIds.map((id) => {
        val idvar = id.toVariable
        And(Implies(LessThan(idvar, zero), GreaterEquals(idvar, IntLiteral(-bound))),
          Implies(GreaterEquals(idvar, zero), LessEquals(idvar, IntLiteral(bound))))
      }).toSeq)
      
      val elapsedTime = System.currentTimeMillis() - startTime
      val remTime = (timeoutMillis - elapsedTime)/1000
      val cegisCore = new CegisCore(context, program, remTime.toInt)
      val (res, ctr, model) = cegisCore.solve(tempIds, formula, And(currentCtr, boundctr), solveAsInt = true)
      currentCtr = And(ctr, currentCtr)
      res match {
        case None => {
          //time out
          timedout = true          
          currModel = model
        }
        case Some(true) => {
          solved = true          
          currModel = model
        }
        case Some(false) => {
          //increase the bounds here
          bound += incrStep
        }
      }
    }
    
    //this can never return Some(false) as this will never know
    if(solved) {
      (Some(true), currentCtr, currModel)
    } else {
      (None, currentCtr, currModel)
    }    
  }
}

class CegisSolverIncr(context : LeonContext, 
    program : Program,
    rootFun : FunDef,
    ctrTracker : ConstraintTracker, 
    tempFactory: TemplateFactory,    
    timeout: Int,
    bound: Option[Int] = None) extends TemplateSolver(context, program, rootFun, ctrTracker, tempFactory, timeout) {
        
  override def solve(tempIds: Set[Identifier], funcVCs: Map[FunDef, Expr]): (Option[Map[FunDef, Expr]], Option[Set[Call]]) = {
    
    val funcs = funcVCs.keys
    val formula = Or(funcs.map(funcVCs.apply _).toSeq)
    
    //using reals with bounds does not converge and also results in overflow
    val (res, _, model) = (new CegisCoreIncr(context, program, timeout)).solveInSteps(tempIds, formula)
    res match {
      case Some(true) => (Some(getAllInvariants(model)), None)
      case Some(false) => (None, None) //no solution exists 
      case _ => //timed out
        throw IllegalStateException("Timeout!!")
    }
  }  
 }*/