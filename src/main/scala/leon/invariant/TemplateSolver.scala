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

abstract class TemplateSolver (
    context : LeonContext, 
    program : Program,
    rootFun : FunDef,
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
  
  //for debugging 
  private val dumpVC = false
  private val debugMinimization = true
      
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

      if (dumpVC) {
        println("Func: " + fd.id + " VC: " + ScalaPrinter(formulaWithAxioms))
        val filename = "vc-" + FileCountGUID.getID + ".txt"
        val wr = new PrintWriter(new File(filename))
        ExpressionTransformer.PrintWithIndentation(wr, simplifyArithmetic(formulaWithAxioms))
        println("Printed VC of " + fd.id + " to file: " + filename)
        wr.flush()
        wr.close()
      }
      
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
  
  def solve(tempIds : Set[Identifier], funcVCs : Map[FunDef,Expr]) : (Option[Map[FunDef,Expr]], Option[Set[Call]])

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

  /**
   * Here we are assuming that that initModel is a model for ctrs
   * TODO: make sure that the template for rootFun is the time template   
   * TODO: assuming that the value of coefficients in +ve in the solution
   */         
  val MaxIter = 16 //note we may not be able to represent anything beyond 2^16
  val MaxInt = Int.MaxValue
  val sqrtMaxInt = 45000 //this is a number that is close a sqrt of 2^31
  val half= RealLiteral(1,2)
  val two= RealLiteral(2,1)
  val rzero = RealLiteral(0,1)
  val mone = RealLiteral(-1,1)
  
  //for statistics and output
  //store the lowerbounds for each template variables in the template of the rootFun provided it is a time template
  var lowerBoundMap = Map[Variable,RealLiteral]()
  
  import RealValuedExprInterpreter._
  def tightenTimeBounds(inputCtr: Expr, initModel: Map[Identifier, Expr]): Map[Identifier, Expr] = {
    val rootFd = rootFun
    val template = tempFactory.getTemplate(rootFd)
    if (template.isDefined) {

      //the order in which the template variables are minimized is based on the level of nesting of the  terms
      val tempvarNestMap: Map[Variable, Int] = computeCompositionLevel(template.get)      
      val orderedTempVars = tempvarNestMap.toSeq.sortWith((a, b) => a._2 >= b._2).map(_._1)

      //do a binary search on sequentially on each of these tempvars      
      val solver = SimpleSolverAPI(
        new TimeoutSolverFactory(SolverFactory(() => new UIFZ3Solver(context, program)),
          timeout * 1000))

      println("minimizing...")
      var currentModel = initModel
      orderedTempVars.foldLeft(inputCtr: Expr)((acc, tvar) => {
                            
        var upperBound = currentModel(tvar.id).asInstanceOf[RealLiteral]
        //note: the lower bound is an integer by construction
        var lowerBound : Option[RealLiteral] = None
        
        if(this.debugMinimization) {
          println("Minimizing variable: "+ tvar+" Initial upperbound: "+upperBound)          
        }

        //TODO: use incremental solving of z3 here (however make sure there is no bug)
        var continue = true
        var iter = 0
        do {
          iter += 1

          //here we perform some sanity checks to prevent overflow
          if (!boundSanityChecks(upperBound, lowerBound)) {
            continue = false
          } else {
            //we make sure that curr val is an integer
            val currval = if (lowerBound.isDefined) {
              val midval = evaluate(Times(half, Plus(upperBound, lowerBound.get)))
              floor(midval)

            } else {
              val rlit @ RealLiteral(n, d) = upperBound
              if (isGEZ(rlit)) {
                if (n == 0) {
                  //make the upper bound negative 
                  mone
                } else {
                  floor(evaluate(Times(half, upperBound)))
                }
              } else floor(evaluate(Times(two, upperBound)))
            }

            //check if the lowerbound, if it exists, is < currval
            if (lowerBound.isDefined && evaluateRealPredicate(GreaterEquals(lowerBound.get, currval))) {
              continue = false
            } else {
              val boundCtr = if (lowerBound.isDefined) {
                And(LessEquals(tvar, currval), GreaterEquals(tvar, lowerBound.get))
              } else LessEquals(tvar, currval)

              //val t1 = System.currentTimeMillis()
              val (res, newModel) = solver.solveSAT(And(acc, boundCtr))
              //val t2 = System.currentTimeMillis()
              //println((if (res.isDefined) "solved" else "timed out") + "... in " + (t2 - t1) / 1000.0 + "s")
              res match {
                case Some(true) => {
                  //here we have a new upper bound and also a newmodel
                  val newval = newModel(tvar.id).asInstanceOf[RealLiteral]

                  if (newval.hasOverflow) {
                    continue = false
                  } else {
                    upperBound = newval
                    //complete the new model if necessary
                    currentModel = initModel.keys.map((id) => {
                      if (newModel.contains(id))
                        (id -> newModel(id))
                      else
                        (id -> currentModel(id))
                    }).toMap            
                    if (this.debugMinimization)
                      println("Found new upper bound: " + upperBound)
                  }
                }
                case _ => {
                  //here we have a new lower bound: currval
                  lowerBound = Some(currval)

                  if (this.debugMinimization)
                    println("Found new lower bound: " + currval)
                }
              }
            }
          }
        } while (continue && iter < MaxIter)
        //here, we found a best-effort minimum
        if(lowerBound.isDefined) {
          //record the lower bound if it exist
          if(lowerBoundMap.contains(tvar)) {
            lowerBoundMap -= tvar            
          } 
          lowerBoundMap += (tvar -> lowerBound.get)          
        }
          
        And(acc, Equals(tvar, currentModel(tvar.id)))
      })
      println("Minimization complete...")      
      currentModel
    } else
      initModel
  }
  
  /**
   * These checks are performed to avoid an overflow during the computation of currval
   */
  def boundSanityChecks(ub: RealLiteral, lb: Option[RealLiteral]) : Boolean = {
    val RealLiteral(n,d) = ub
    if(n <= (MaxInt / 2)) {
      if(lb.isDefined) {
        val RealLiteral(n2, _) = lb.get
        (n2 <= sqrtMaxInt && d <= sqrtMaxInt)        
      } else {
        (d <= (MaxInt /2))
      }
    } else false
  }

  /**
   * The following code is little tricky
   */
  def computeCompositionLevel(template: Expr): Map[Variable, Int] = {
    var nestMap = Map[Variable, Int]()

    def updateMax(v: Variable, level: Int) = {
      println("Update: "+v+"-->"+level)
      if (nestMap.contains(v)) {
        if (nestMap(v) < level) {
          nestMap -= v
          nestMap += (v -> level)
        }
      } else
        nestMap += (v -> level)
    }

    def functionNesting(e: Expr): Int = {
      //println("NestExpr: " + e)
      e match {

        case Times(e1, v @ Variable(id)) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          val nestLevel = functionNesting(e1)
          updateMax(v, nestLevel)
          nestLevel
        }
        case Times(v @ Variable(id), e2) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          val nestLevel = functionNesting(e2)
          updateMax(v, nestLevel)
          nestLevel
        }
        case v @ Variable(id) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          updateMax(v, 0)
          0
        }
        case FunctionInvocation(_, args) => 1 + args.foldLeft(0)((acc, arg) => acc + functionNesting(arg))
        case t: Terminal => 0
        case UnaryOperator(arg, _) => functionNesting(arg)
        case BinaryOperator(a1, a2, _) => functionNesting(a1) + functionNesting(a2)
        case NAryOperator(args, _) => args.foldLeft(0)((acc, arg) => acc + functionNesting(arg))
      }
    }
    functionNesting(template)
    nestMap
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