package leon
package invariant.engine

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers._
import solvers.z3.FairZ3Solver
import java.io._
import purescala.ScalaPrinter
import verification._
import scala.reflect.runtime.universe

import invariant.templateSolvers._
import invariant.factories._
import invariant.util._
import invariant.util.Util._
import invariant.structure._
import invariant.transformations._

/**
 * @author ravi
 * This phase performs automatic invariant inference.
 * TODO: Fix the handling of getting a template for a function, the current code is very obscure
 * TODO: Do we need to also assert that time is >= 0
 */
class InferenceEngineGenerator(ctx: InferenceContext, 
    tempSolverFactory : (ConstraintTracker, TemplateFactory, FunDef) => TemplateSolver) {

  val reporter = ctx.reporter
  val program = ctx.program
  val fls = BooleanLiteral(false)
  val tru = BooleanLiteral(true)

  def getInferenceEngine(funDef: FunDef, tempFactory: TemplateFactory): (() => (Option[Boolean], Option[Map[FunDef,Expr]])) = {
    //create a body and post of the function
    val body = funDef.nondetBody.get
    val (resid, post) = funDef.postcondition.get
    val resvar = resid.toVariable
         
    val simpBody = matchToIfThenElse(body)
    val plainBody = Equals(resvar, simpBody)    
    val bodyExpr = if (funDef.hasPrecondition) {
      And(matchToIfThenElse(funDef.precondition.get), plainBody)
    } else plainBody        
    
    val postExpr = matchToIfThenElse(post)       
    //create a postcondition template if the function is recursive or if a template is provided for the function
    val funinfo = FunctionInfoFactory.getFunctionInfo(funDef)
    val cg = CallGraphUtil.constructCallGraph(program, onlyBody = true)
    val postTemp = if (cg.isRecursive(funDef) || (funinfo.isDefined && funinfo.get.hasTemplate)) {
      //this is a way to create an idenitity map :-))
      val selfInv = FunctionInvocation(TypedFunDef(funDef,funDef.tparams.map(_.tp)) , funDef.params.map(_.toVariable))
      val argmap = Util.formalToAcutal(Call(resvar, selfInv))
      Some(tempFactory.constructTemplate(argmap, funDef))      
    } else None    
    val fullPost = if (postTemp.isDefined) {
      if (postExpr == tru) postTemp.get
      else And(postExpr, postTemp.get)
    } else postExpr
    if (fullPost == tru) {
      throw new IllegalStateException("post is true, nothing to be proven!!")
    }
        
    val vcExpr = ExpressionTransformer.normalizeExpr(And(bodyExpr,Not(fullPost)), ctx.multOp)
    //for debugging
    println("falttened VC: " + ScalaPrinter(vcExpr))   
    
    //Create and initialize a constraint tracker
    val constTracker = new ConstraintTracker(ctx, funDef, tempFactory)
    constTracker.addVC(funDef, vcExpr)    

    val tempSolver = tempSolverFactory(constTracker, tempFactory, funDef)
    //refinement engine state
    var refinementStep: Int = 0
    var toRefineCalls : Option[Set[Call]] = None
    
    val inferenceEngine = () => {

      Stats.updateCounter(1, "VC-refinement")
      /* uncomment if we want to bound refinements
       * if (refinementStep >= 5)
          throw IllegalStateException("Done 4 refinements")*/
           
      val refined =
        if (refinementStep >= 1) {

          reporter.info("- More unrollings for invariant inference")

          val toUnrollCalls = if(ctx.targettedUnroll) toRefineCalls else None
          val unrolledCalls = constTracker.refineVCs(toUnrollCalls)          
          if (unrolledCalls.isEmpty) {
            reporter.info("- Cannot do more unrollings, reached unroll bound")
            false
          } else true
          
        } else {          
          constTracker.initialize
          true
        } 

      refinementStep += 1

      if (!refined) (Some(false), None)
      else {
        //solve for the templates in this unroll step          
        val (res, callsInPath) = tempSolver.solveTemplates()
        toRefineCalls = callsInPath

        if (res.isDefined) {

          var output = "Invariants for Function: " + funDef.id + "\n"
          res.get.foreach((pair) => {
            val (fd, inv) = pair                                    
            val simpInv = simplifyArithmetic(replaceInstruVars(multToTimes(inv, ctx),fd))
            reporter.info("- Found inductive invariant: " + fd.id + " --> " + ScalaPrinter(simpInv))
            output += fd.id + " --> " + simpInv + "\n"
          })
          //add invariants to stats
          SpecificStats.addOutput(output)          

          reporter.info("- Verifying Invariants... ")

          val verifierRes = verifyInvariant(res.get, funDef)
          //if (res.get.contains(funDef)) res.get(funDef) else BooleanLiteral(true)
          //val verifierRes = (Some(false),Map())
          val finalRes = verifierRes._1 match {
            case Some(false) => {
              reporter.info("- Invariant verified")
              //return the invariant for the root function
              (Some(true), Some(res.get))
            }
            case Some(true) => {
              reporter.error("- Invalid invariant, model: " + verifierRes._2)
              throw IllegalStateException("")
            }
            case _ => {
              //the solver timed out here
              reporter.error("- Unable to prove or disprove invariant, the invariant is probably true")
              //return the invariant for the root function
              (Some(true), Some(res.get))
            }
          }                            
          //check for invariant strength          
          finalRes
          
        } else {
          //here, we do not know if the template is solvable or not, we need to do more unrollings.
          (None, None)
        }
      }
    }
    inferenceEngine
  }
  
  /**
   * This function creates a new program with each function postcondition strengthened by
   * the inferred postcondition   
   */
  def verifyInvariant(newposts: Map[FunDef, Expr], rootfd: FunDef): (Option[Boolean], Map[Identifier, Expr]) = {

    //create a fundef for each function in the program that is not "mult"
    val newFundefs = program.definedFunctions.collect {
      case fd @ _ if (fd != ctx.multfun && fd != ctx.pivmultfun) => {
        val newfd = new FunDef(FreshIdentifier(fd.id.name, false), fd.tparams, fd.returnType, fd.params)
        (fd, newfd)
      }
    }.toMap

    //note important, we must also replace "mult" function by "Times"
    val replaceFun = (e: Expr) => e match {
      case FunctionInvocation(fd, args) if fd == ctx.multfun => {
        Times(args(0), args(1))
      }
      case fi @ FunctionInvocation(tfd1, args) if newFundefs.contains(tfd1.fd) =>
        FunctionInvocation(TypedFunDef(newFundefs(tfd1.fd), tfd1.tps), args)
      case _ => e
    }

    //create a body, pre, post for each newfundef
    newFundefs.foreach((entry) => {
      val (fd, newfd) = entry

      //add a new precondition
      newfd.precondition =
        if (fd.precondition.isDefined)
          Some(simplePostTransform(replaceFun)(fd.precondition.get))
        else None

      //add a new body
      newfd.body = if (fd.hasBody)
        Some(simplePostTransform(replaceFun)(fd.body.get))
      else None

      //add a new postcondition                  
      val newpost = if (newposts.contains(fd)) {
        val inv = newposts(fd)
        if (fd.postcondition.isDefined) {
          val (resvar, postExpr) = fd.postcondition.get
          Some((resvar, And(postExpr, inv)))
        } else {
          //replace #res in the invariant by a new result variable
          val resvar = FreshIdentifier("res", true).setType(fd.returnType)
          val ninv = replace(Map(ResultVariable() -> resvar.toVariable), inv)
          Some((resvar, ninv))
        }
      } else fd.postcondition

      newfd.postcondition = if (newpost.isDefined) {
        val (resvar, pexpr) = newpost.get
        Some(resvar, simplePostTransform(replaceFun)(pexpr))
      } else None
    })

    val augmentedProg = Util.copyProgram(program, (defs :Seq[Definition]) => defs.collect {
      case fd: FunDef if(newFundefs.contains(fd)) => newFundefs(fd)
      case d if(!d.isInstanceOf[FunDef]) => d
    })    
    /*val newDefs = program.defs.collect {
      case fd: FunDef if(newFundefs.contains(fd)) => newFundefs(fd)
      case d if(!d.isInstanceOf[FunDef]) => d
    }*/
    //val augmentedProg = program.copy(mainObject = program.mainObject.copy(defs = newDefs))
    
    //convert the program back to an integer program if necessary
    val (newprog, newroot) = if (ctx.usereals) {
      val realToIntconverter = new RealToIntProgram()
      val intProg = realToIntconverter(augmentedProg)
      (intProg, realToIntconverter.mappedFun(newFundefs(rootfd)))      
    } else {
      (augmentedProg,newFundefs(rootfd))
    }
    //println("Program: "+newprog)
    //println(ScalaPrinter(newprog))

    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(newprog)
    val vc = defaultTactic.generatePostconditions(newroot)(0)

    val verifyTimeout = 5
    val fairZ3 = new SimpleSolverAPI(
      new TimeoutSolverFactory(SolverFactory(() => new FairZ3Solver(ctx.leonContext, newprog) with TimeoutSolver),
        verifyTimeout * 1000))
    //println("Func : "+ vc.funDef + " new vc: "+vc.condition)            
    val sat = fairZ3.solveSAT(Not(vc.condition))
    //    if(sat._1 == Some(true)){
    //      val evaluator = new DefaultEvaluator(ctx, newprog)
    //      
    //      simplePostTransform((e: Expr) => e match {
    //        case FunctionInvocation(_,_) => {
    //          println(e + " --> "+evaluator.eval(e, sat._2))
    //          e
    //        }
    //        case _ => e
    //      })(vc.condition)      
    //    }
    sat
  }
  
//  def testInvairantStrength(tempSolver: TemplateSolver, invs: Map[Identifier,Expr], rootFun : FunDef) : Unit = {
//    //now verify the lower bounds                  
//          val lbModel = tempSolver.lowerBoundMap.map((entry) => (entry._1.id -> entry._2.asInstanceOf[Expr]))
//          val lbExpr = TemplateInstantiator.getAllInvariants(lbModel, Map(funDef -> tempFactory.getTemplate(funDef).get))
//          val counterRes = verifyInvariant(lbExpr, funDef)         
//          counterRes._1 match {
//            case Some(false) => {
//              val out = "Found stronger inductive invariant: "+lbExpr
//              Stats.addLowerBoundStats(funDef, tempSolver.lowerBoundMap, out)
//              reporter.error("- " + out)          
//            }
//            case Some(true) => {
//              val out = "Found counter example for lower bound"
//              Stats.addLowerBoundStats(funDef, tempSolver.lowerBoundMap, out)
//              reporter.error(out )             
//            }
//            case _ => {
//              val out = "Timeout on disproving lower bound"
//              Stats.addLowerBoundStats(funDef, tempSolver.lowerBoundMap, out)
//              //the solver timed out here
//              reporter.error("- "+out)              
//            }            
//          }
//  }
}
