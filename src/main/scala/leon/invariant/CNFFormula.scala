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

//A conjunctive normal form (CNF) formula
//'initexpr' is required to be in negation normal form and And/Ors have been pulled up   
class Formula(initexpr: Expr) {
  
  val fls = BooleanLiteral(false)
  val tru = BooleanLiteral(true)
  //protected val debugInstrumentation = false
  
  protected var disjuncts = Map[Variable, Seq[Constraint]]() //a mapping from guards to conjunction of atoms
  protected var conjuncts = Map[Variable, Expr]() //a mapping from guards to disjunction of atoms
  protected var root : Variable = addConstraints(initexpr)._1
  
  def disjunctsInFormula = disjuncts 
  
  //return the root variable and the sequence of disjunct guards added 
  //(which includes the root variable incase it respresents a disjunct)
  def addConstraints(ine: Expr) : (Variable, Seq[Variable]) = {
    
    var newDisjGuards = Seq[Variable]()    
    
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
            newDisjGuards :+= g
            //println("atoms: "+atoms)
            val ctrs = getCtrsFromExprs(atoms)            
            disjuncts += (g -> ctrs)                
            g
          }
        })
        //create a temporary for Or
        val gor = TVarFactory.createTemp("b").setType(BooleanType).toVariable
        val newor = Or(newargs)        
        conjuncts += (gor -> newor)
        gor
      }
      case _ => e
    })(ine)
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
        newDisjGuards :+= g
        disjuncts += (g -> ctrs)        
        g
      }
    }
    (rootvar, newDisjGuards)
  }
  
  def pickSatDisjunct(model: Map[Identifier, Expr]): Seq[Constraint] = {
        
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
      val guards = ctrs.collect {
        case BoolConstraint(v @ Variable(_)) if (conjuncts.contains(v)) => v
      }
      if (guards.isEmpty) Seq()
      else {
        guards.foldLeft(Seq[Variable]())((acc, g) => {
          if (model(g.id) != tru)
            throw IllegalStateException("Not a satisfiable guard: " + g)

          if (conjuncts.contains(g))
            acc ++ traverseOrs(g, model)
          else {
            acc ++ (g +: traverseAnds(g, model))
          }
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
  
  //'neweexpr' is required to be in negation normal form and And/Ors have been pulled up  
  def conjoinWithDisjunct(guard: Variable, newexpr: Expr) : (Variable, Seq[Variable]) = {
     val (exprRoot, newGaurds) = addConstraints(newexpr)
     //add 'newguard' in conjunction with 'disjuncts(guard)'
     val ctrs = disjuncts(guard)
     disjuncts -= guard
     disjuncts += (guard -> (BoolConstraint(exprRoot) +: ctrs))
     (exprRoot, newGaurds)
  }
  
  def conjoinWithRoot(newexpr: Expr) : (Variable, Seq[Variable]) = {
    if(disjuncts.contains(root))  
      conjoinWithDisjunct(root, newexpr)
    else {
      val (exprRoot, newGaurds) = addConstraints(newexpr)
      //update root
      val newRoot = TVarFactory.createTemp("b").setType(BooleanType).toVariable
      disjuncts += (newRoot -> Seq(BoolConstraint(root), BoolConstraint(exprRoot)))
      root = newRoot      
      (exprRoot, newGaurds)
    }
  }
  
  def toExpr : Expr={
    val disjs = disjuncts.map((entry) => {
      val (g,ctrs) = entry
      Equals(g, And(ctrs.map(_.toExpr)))
    }).toSeq
    val conjs = conjuncts.map((entry) => Equals(entry._1, entry._2)).toSeq
    And((disjs ++ conjs) :+ root)
  } 
}
