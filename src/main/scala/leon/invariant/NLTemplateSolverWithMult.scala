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
import leon.purescala.ScalaPrinter
import leon.plugin.DepthInstPhase
import ExpressionTransformer._

class NLTemplateSolverWithMult(ctx : InferenceContext, rootFun: FunDef,
  ctrTracker: ConstraintTracker, tempFactory: TemplateFactory) 
  extends NLTemplateSolver(ctx, rootFun, ctrTracker, tempFactory) {
     
  val axiomFactory = new AxiomFactory(ctx)
  
  override def getVCForFun(fd: FunDef): Expr = {    
    val plainvc = ctrTracker.getVC(fd).toExpr
    val nlvc = Util.multToTimes(plainvc, ctx)
    IntLiteralToReal(nlvc)
  }
  
  override def splitVC(fd: FunDef) : (Expr,Expr) = {
    val (paramPart, rest) = ctrTracker.getVC(fd).splitParamPart   
    (IntLiteralToReal(Util.multToTimes(paramPart, ctx)),IntLiteralToReal(Util.multToTimes(rest, ctx)))
  }
    
  override def instantiateTemplate(e: Expr, tempVarMap: Map[Expr, Expr]) : Expr = {
    replace(tempVarMap, e)
  }
  
  override def predEval(model: Map[Identifier, Expr]): (Expr => Boolean) = {        
    def modelVal(id: Identifier): RealLiteral = model(id).asInstanceOf[RealLiteral]    
    (e: Expr) => e match {
      case Iff(Variable(id1),Variable(id2)) => model(id1) == model(id2)
      case Equals(Variable(id1),Variable(id2)) => model(id1) == model(id2) //note: ADTs can also be compared for equality
      case BinaryOperator(Variable(id1), Variable(id2), op) if (e.isInstanceOf[LessThan] 
        || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
        || e.isInstanceOf[GreaterEquals]) => {
          
        	RealValuedExprInterpreter.evaluateRealPredicate(op(modelVal(id1),modelVal(id2)))
        }      
      case _ => throw IllegalStateException("Predicate not handled: " + e)
    }
  }
  
  //TODO: for soundness we need to override 'doesSatisfyModel' as well
  
  override def axiomsForTheory(formula : Formula, calls: Set[Call], model: Map[Identifier,Expr]) : Seq[Constraint] = {
  
    //in the sequel we instantiate axioms for multiplication
    val inst1 = unaryMultAxioms(formula, calls, predEval(model))
    val inst2 = binaryMultAxioms(formula,calls, predEval(model))         
    val multCtrs = (inst1 ++ inst2).map(ConstraintUtil.createConstriant _)                     
    
    Stats.updateCounterStats(multCtrs.size, "MultAxiomBlowup", "disjuncts")
    ctx.reporter.info("Number of multiplication induced predicates: "+multCtrs.size)
    multCtrs
  }

  def chooseSATPredicate(expr: Expr, predEval: (Expr => Boolean)): Expr = {
    val norme = ExpressionTransformer.normalizeExpr(expr,ctx.multOp)
    val preds = norme match {
      case Or(args) => args
      case BinaryOperator(_, _, _) => Seq(norme)
      case _ => throw IllegalStateException("Not(ant) is not in expected format: " + norme)
    }
    //pick the first predicate that holds true
    preds.collectFirst { case pred @ _ if predEval(pred) => pred }.get

  } 
  
  def isMultOp(call : Call) : Boolean = {
    (call.fi.funDef == ctx.multfun || call.fi.funDef == ctx.pivmultfun) 
  }
  
  def unaryMultAxioms(formula: Formula, calls: Set[Call], predEval: (Expr => Boolean)) : Seq[Expr] = {
    val axioms = calls.flatMap {
      case call@_ if (isMultOp(call) && axiomFactory.hasUnaryAxiom(call)) => {        
        val (ant,conseq) = axiomFactory.unaryAxiom(call)
        if(predEval(ant)) 
          Seq(ant,conseq)
        else 
          Seq(chooseSATPredicate(Not(ant), predEval))
      }
      case _ => Seq()
    }
    axioms.toSeq
  }
  
  def binaryMultAxioms(formula: Formula, calls: Set[Call], predEval: (Expr => Boolean)) : Seq[Expr] = {

    val mults = calls.filter(call => isMultOp(call) && axiomFactory.hasBinaryAxiom(call))    
    val product = Util.cross(mults,mults).collect{ case (c1,c2) if c1 != c2 => (c1,c2) }
    
    ctx.reporter.info("Theory axioms: "+product.size)
    Stats.updateCumStats(product.size, "-Total-theory-axioms")

    val newpreds = product.flatMap(pair => {      
      val axiomInsts = axiomFactory.binaryAxiom(pair._1, pair._2)      
      axiomInsts.flatMap {        
        case (ant,conseq) if predEval(ant) => Seq(ant,conseq) 			//if axiom-pre holds. 
        case (ant,_) => Seq(chooseSATPredicate(Not(ant), predEval))		//if axiom-pre does not hold.
      }
    })                    
    newpreds.toSeq
  }  
}
