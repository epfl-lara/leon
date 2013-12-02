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
    
    solve(tempIds,funcVCs, initCtr)
  }
  
  def solve(tempIds: Set[Identifier], funcVCs: Map[FunDef, Expr], initCtr : Expr)
  : Option[Map[FunDef, Expr]] = {
    
    val funcs = funcVCs.keys
    val solver = SimpleSolverAPI(
      new TimeoutSolverFactory(SolverFactory(() => new UIFZ3Solver(context, program)),
        timeout * 1000))           

    val notVC = simplePostTransform((e) => e match {
      case Equals(_, FunctionInvocation(_, _)) => tru
      case Iff(_, FunctionInvocation(_, _)) => tru
      case _ => e
    })(Not(Or(funcs.map(funcVCs.apply _).toSeq)))
    
    var oldModels = Set[Expr]()
    def addModel(m : Map[Identifier, Expr]) = {
      val mexpr = InvariantUtil.modelToExpr(m)
      if(oldModels.contains(mexpr))
        throw IllegalStateException("repeating model !!:"+ m)
      else oldModels += mexpr 
    }
    //add the initial model
    val simplestModel = tempIds.map((id) => (id -> simplestValue(id.toVariable))).toMap
    addModel(simplestModel)
    
    def cegisRec(model: Map[Identifier, Expr], inputCtr: Expr): Option[Map[FunDef, Expr]] = {
      //for stats
      Stats.cegisIterations += 1

      /*println("candidate Invariants")
      val candInvs = getAllInvariants(model)
      candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))*/
    
      val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable, elem._2)).toMap
      val instVC = Or(funcs.foldLeft(Seq[Expr]())((acc, fd) => {
        acc :+ simplifyArithmetic(TemplateInstantiator.instantiate(funcVCs(fd), tempVarMap))
      }))
      //println("instvc: "+instVC)
      val spuriousTempIds = variablesOf(instVC).intersect(TemplateIdFactory.getTemplateIds)
      if (!spuriousTempIds.isEmpty)
        throw IllegalStateException("Found a template variable in instvc: " + spuriousTempIds)

      //println("solving instantiated vcs...")
      val t1 = System.currentTimeMillis()
      val (res, progModel) = solver.solveSAT((new RealToInt()).mapRealToInt(instVC))
      val t2 = System.currentTimeMillis()
      if (res.isDefined && res.get == true) {
        println("1: solved... in " + (t2 - t1) / 1000.0 + "s")
        //instantiate vcs with newmodel
        val progVarMap: Map[Expr, Expr] = progModel.map((elem) => (elem._1.toVariable, elem._2)).toMap                       
        val tempctrs = replace(progVarMap, notVC)
        //println("Tempctrs: "+Not(Or(funcs.map(funcExprs.apply _).toSeq)))

        val spuriousProgIds = variablesOf(tempctrs).filterNot(TemplateIdFactory.IsTemplateIdentifier _)
        if (!spuriousProgIds.isEmpty)
          throw IllegalStateException("Found a progam variable in tempctrs: " + spuriousProgIds)

        //val modelToExpr = InvariantUtil.modelToExpr(model)
        val newctr = And(tempctrs, inputCtr)
        //for stats
        val (cum, max) = Stats.cumMax(Stats.cumTemplateCtrSize, Stats.maxTemplateCtrSize, InvariantUtil.atomNum(newctr))
        Stats.cumTemplateCtrSize = cum; Stats.maxTemplateCtrSize = max;

        /*println("vc: "+vc)
      println("Prog Model: "+ progModel)      
      println("tempctr: "+tempconstr)*/

        //println("solving template constriants...")
        val t3 = System.currentTimeMillis()
        //convert templates to integers and solve
        val realToInt = new RealToInt()
        val (res1, intModel) = solver.solveSAT(realToInt.mapRealToInt(newctr))
        //reconvert integer models for templates to real models
        val newModel = realToInt.unmapModel(intModel)
        val t4 = System.currentTimeMillis()
        if (res1.isDefined) {
          //try with the new model
          if (res1.get == false) {
            None //cannot solve templates
          } else {
            println("2: solved... in " + (t4 - t3) / 1000.0 + "s")
            //println("New model: "+newModel)
            addModel(newModel)
            cegisRec(newModel, newctr)
          }
        } else
          throw IllegalStateException("2: timed out... in " + (t4 - t3) / 1000.0 + "s")

      } else if (res.isDefined && res.get == false) {
        //found inductive invariant
        Some(getAllInvariants(model))
      } else
        throw IllegalStateException("1: timed out... in " + (t2 - t1) / 1000.0 + "s")
    }

    cegisRec(simplestModel, initCtr)
  }
 }
