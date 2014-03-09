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

class ConstraintTracker(rootFun : FunDef, context:LeonContext, program: Program, temFactory: TemplateFactory) {
    
  //some constants
  protected val zero = IntLiteral(0)
  protected val one = IntLiteral(1)
  protected val mone =IntLiteral(-1)   
  protected val fls = BooleanLiteral(false)
  protected val tru = BooleanLiteral(true)
  
  //for debugging
  protected val debugInstrumentation = false  
  
  //a mapping from guards to conjunction of atoms  
  protected var disjuncts = Map[Variable, Seq[Constraint]]()
  //a mapping from guards to disjunction of atoms
  protected var conjuncts = Map[Variable, Expr]()
  //a mapping from function vcs to the root guard (before instantiation of axioms)
  protected var vcRoots = Map[FunDef, Variable]()
  //a mapping from axioms keys (for now pairs of calls) to the guards
  protected var axiomRoots = Map[(Expr,Expr),Variable]()
  
  //a mapping from functions to its VCs represented as a list of formulas that should be conjoined.
  protected var funcVCs = Map[FunDef,List[Expr]]()
  
  protected val vcRefiner = new RefinementEngine(program, this, temFactory, context)
  protected val axiomInstatiator = new AxiomInstantiator(context, program, this)
  
  def getFuncs : Seq[FunDef] = funcVCs.keys.toSeq
  def hasVCs(fdef: FunDef) = funcVCs.contains(fdef)  
  def getVC(fd: FunDef) : Seq[Expr] = funcVCs(fd)
  
  def instrumentWithGuards(formula: Expr): (Variable, Expr) = {
    
    def getCtrsFromExprs(exprs: Seq[Expr]) : Seq[Constraint] = {
      var break = false
      exprs.foldLeft(Seq[Constraint]())((acc, e) => {
        if (break) acc
        else {
          val ctr = ConstraintUtil.createConstriant(e)
          ctr match {
            case BoolConstraint(BooleanLiteral(true)) => acc
            case BoolConstraint(BooleanLiteral(false)) => {
              break = true
              Seq(ctr)
            }
            case _ => acc :+ ctr
          }
        }
      })
    }
    
    //Assuming that VC is in negation normal form and And/Ors have been pulled up
    var implications = Seq[Expr]()
    val f1 = simplePostTransform((e: Expr) => e match {
      case Or(args) => {
        val newargs = args.map(arg => arg match {
          case v: Variable if (disjuncts.contains(v)) => arg
          case v: Variable if (conjuncts.contains(v)) => throw IllegalStateException("or gaurd inside conjunct: "+e+" or-guard: "+v)
          case _ => {
            val atoms = arg  match {
              case And(atms) => atms
              case _ => Seq(arg)
            }              
            val g = TVarFactory.createTemp("b").setType(BooleanType).toVariable  
            //println("atoms: "+atoms)
            val ctrs = getCtrsFromExprs(atoms)            
            disjuncts += (g -> ctrs) 
            
            //important: here we cannot directly use "atoms" as conversion to constraints performs some syntactic changes 
            val newe = Equals(g, And(ctrs.map(_.toExpr)))
            implications :+= newe
            g
          }
        })
        //create a temporary for Or
        val gor = TVarFactory.createTemp("b").setType(BooleanType).toVariable
        val newor = Or(newargs)
        val newe = Equals(gor, newor)
        conjuncts += (gor -> newor)
        implications :+= newe
        gor
      }
      case _ => e
    })(formula)
    val rootvar = f1 match {      
      case v: Variable if(conjuncts.contains(v)) => v
      case v: Variable if(disjuncts.contains(v)) => throw IllegalStateException("f1 is a disjunct guard: "+v)
      case _ => {
        val atoms = f1 match {
          case And(atms) => atms
          case _ => Seq(f1)
        }
        val g = TVarFactory.createTemp("b").setType(BooleanType).toVariable
        val ctrs = getCtrsFromExprs(atoms)
        disjuncts += (g -> ctrs)
        val newe = Equals(g, And(ctrs.map(_.toExpr)))
        implications :+= newe
        g
      }
    }    
    
    if(this.debugInstrumentation) {
      println("After Instrumentation: ")
      implications.foreach(println _ )
      println(rootvar)
    }
      
    val instruFormula = And(implications :+ rootvar)
    (rootvar, instruFormula)
  }
 
  def conjoinWithVC(fd: FunDef, vcPart: Expr) {
     val vcList = funcVCs(fd)
     funcVCs -= fd
     funcVCs += (fd -> (vcPart +: vcList))                   
  }
  
  def addVC(fd: FunDef, vc: Expr) = {
    val (rg, formula) = instrumentWithGuards(vc)
    vcRoots += (fd -> rg)    
    funcVCs += (fd -> List(formula))   
    //add axioms    
  }

  def refineVCs(toUnrollCalls: Option[Set[Call]]) : Set[Call]  = {
    val unrolledCalls = vcRefiner.refineAbstraction(toUnrollCalls)    
    //add axioms
    
    unrolledCalls
  }  
  
  //'root' is required to be guard variable
  def pickSatDisjunct(root: Variable, model: Map[Identifier, Expr]): Seq[Constraint] = {

    def traverseOrs(gd: Variable, model: Map[Identifier, Expr]): Seq[Variable] = {
      val e @ Or(guards) = conjuncts(gd)
      //pick one guard that is true
      val guard = guards.collectFirst { case g @ Variable(id) if (model(id) == tru) => g }
      if (!guard.isDefined)
        throw IllegalStateException("No satisfiable guard found: " + e)
      guard.get +: traverseAnds(guard.get, model)
    }

    def traverseAnds(gd: Variable, model: Map[Identifier, Expr]): Seq[Variable] = {
      val ctrs = disjuncts(gd)
      val orGuards = ctrs.collect {
        case BoolConstraint(v @ Variable(_)) if (conjuncts.contains(v)) => v
      }
      if (orGuards.isEmpty) Seq()
      else {
        orGuards.foldLeft(Seq[Variable]())((acc, g) => {
          if (model(g.id) != tru)
            throw IllegalStateException("Not a satisfiable guard: " + g)
          acc ++ traverseOrs(g, model)
        })
      }
    }
    //if root is unsat return empty
    if (model(root.id) == fls) Seq()
    else {
      val satGuards = if (conjuncts.contains(root)) traverseOrs(root, model)
      else (root +: traverseAnds(root, model))
      satGuards.flatMap(g => disjuncts(g))
    }
  }
  
}