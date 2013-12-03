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
    ctrTracker : ConstraintTracker, 
    tempFactory: TemplateFactory,    
    timeout: Int,
    bound: Option[Int] = None) extends TemplateSolver(context, program, ctrTracker, tempFactory, timeout) {
        
  override def solve(tempIds: Set[Identifier], funcVCs: Map[FunDef, Expr]): Option[Map[FunDef, Expr]] = {

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
    
    val (res, _, model) = (new CegisCore(context, program, timeout)).solve(tempIds, formula, initCtr)
    res match {
      case Some(true) => Some(getAllInvariants(model))
      case Some(false) => None //no solution exists 
      case _ => //timed out
        throw IllegalStateException("Timeout!!")
    }
  }
    
  /**
   * Finds a model for the template variables in the 'formula' so that 'formula' is falsified
   * subject to the constraints on the template variables given by the 'envCtrs'
   */
  
 }

class CegisCore(context : LeonContext, 
    program : Program,
    timeout: Int,
    incrStep : Int = 5) {
  
  val fls = BooleanLiteral(false)
  val tru = BooleanLiteral(true)
  val zero = IntLiteral(0)
  val timeoutMillis = timeout.toLong * 1000

  /*def solveInSteps(tempIds: Set[Identifier], formula: Expr, initCtr: Expr): (Option[Boolean], Expr, Map[Identifier, Expr]) = {
    //start with a bound of |1| and increase in steps given by incrStep
    var bound = 1
    var timeout = false
    var solved = false
    var currCtr : Expr = tru
    var currModel = Map[Identifier, Expr]()    
    
    while(!solved && !timeout) {
      
      val boundctr = And(tempIds.map((id) => {
        val idvar = id.toVariable
        And(Implies(LessThan(idvar, zero), GreaterEquals(idvar, IntLiteral(-bound))),
          Implies(GreaterEquals(idvar, zero), LessEquals(idvar, IntLiteral(bound))))
      }).toSeq)
      
      val (res, ctr, model) = solve(tempIds, formula, And(initCtr, boundctr))
      res match {
        case None => {
          //time out
          timeout = true
          currCtr = ctr
          currModel = model
        }
        case Some(true) => {
          solved = true
          currCtr = ctr
          currModel = model
        }
        case Some(false) => {
          //increase the bound here
          bound += incrStep
        }
      }
    }
    
    //this can never return Some(false) as this will never know
    if(solved) {
      (Some(true), currCtr, currModel)
    } else {
      (None, currCtr, currModel)
    }    
  }
  */
  def solve(tempIds: Set[Identifier], formula: Expr, initCtr: Expr): (Option[Boolean], Expr, Map[Identifier, Expr]) = {
    
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
    val simplestModel = tempIds.map((id) => (id -> simplestValue(id.toVariable))).toMap
    addModel(simplestModel)

    def cegisRec(model: Map[Identifier, Expr], prevctr: Expr): (Option[Boolean], Expr, Map[Identifier, Expr]) = {
      
      val elapsedTime = (System.currentTimeMillis() - startTime)
      if (elapsedTime >= timeoutMillis - 100) {
        //if we have timed out return the present set of constrains and the current model we have
        (None, prevctr, model)
      } else {

        //println("elapsedTime: "+elapsedTime / 1000+" timeout: "+timeout)
        if (InferInvariantsPhase.dumpStats)
          Stats.cegisIterations += 1

        /*println("candidate Invariants")
      val candInvs = getAllInvariants(model)
      candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))*/

        val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable, elem._2)).toMap
        val instFormula = simplifyArithmetic(TemplateInstantiator.instantiate(formula, tempVarMap))

        val spuriousTempIds = variablesOf(instFormula).intersect(TemplateIdFactory.getTemplateIds)
        if (!spuriousTempIds.isEmpty)
          throw IllegalStateException("Found a template variable in instFormula: " + spuriousTempIds)

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
            val tempctrs = simplePreTransform((e) => e match {
              //is 'e' free of template variables ? 
              case _ if (variablesOf(e).filter(TemplateIdFactory.IsTemplateIdentifier _).isEmpty) => {
                //evaluate the term
                val value = solver1.evalExpr(e)
                if (value.isDefined) value.get
                else throw IllegalStateException("Cannot evaluate expression: " + e)
              }
              case _ => e
            })(Not(formula))

            //free the solver
            solver1.free()

            //sanity check
            val spuriousProgIds = variablesOf(tempctrs).filterNot(TemplateIdFactory.IsTemplateIdentifier _)
            if (!spuriousProgIds.isEmpty)
              throw IllegalStateException("Found a progam variable in tempctrs: " + spuriousProgIds)

            val newctr = And(tempctrs, prevctr)

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

            //convert templates to integers and solve. Finally, re-convert integer models for templates to real models
            val realToInt = new RealToInt()
            val (res1, intModel) = solver2.solveSAT(realToInt.mapRealToInt(newctr))
            val newModel = realToInt.unmapModel(intModel)
            val t4 = System.currentTimeMillis()
            println("2: " + (if (res.isDefined) "solved" else "timedout") + "... in " + (t4 - t3) / 1000.0 + "s")

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
    cegisRec(simplestModel, initCtr)
  }
}
