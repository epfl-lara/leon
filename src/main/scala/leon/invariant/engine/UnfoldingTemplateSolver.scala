/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.engine

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.DefOps._
import purescala.ScalaPrinter
import purescala.Constructors._

import solvers._
import verification._
import invariant.factories._
import invariant.util._
import invariant.structure._
import transformations._
import FunctionUtils._
import Util._
import PredicateUtil._
import ProgramUtil._

/**
 * @author ravi
 * This phase performs automatic invariant inference.
 * TODO: Do we need to also assert that time is >= 0
 */
case class InferResult(res: Boolean, model: Option[Model], inferredFuncs: List[FunDef]) {
}

trait FunctionTemplateSolver {
  def apply(): Option[InferResult]
}

class UnfoldingTemplateSolver(ctx: InferenceContext, program: Program, rootFd: FunDef) extends FunctionTemplateSolver {

  val reporter = ctx.reporter
  val debugVCs = false

  lazy val constTracker = new ConstraintTracker(ctx, program, rootFd)
  lazy val templateSolver = TemplateSolverFactory.createTemplateSolver(ctx, program, constTracker, rootFd)

  def constructVC(funDef: FunDef): (Expr, Expr, Expr) = {
    val Lambda(Seq(ValDef(resid)), _) = funDef.postcondition.get
    val body = Equals(resid.toVariable, funDef.body.get)
    val funName = fullName(funDef, useUniqueIds = false)(program)
    val assumptions =
      if (funDef.usePost && ctx.isFunctionPostVerified(funName))
        createAnd(Seq(funDef.getPostWoTemplate, funDef.precOrTrue))
      else funDef.precOrTrue
    val fullPost =
      if (funDef.hasTemplate) {
        // if the postcondition is verified do not include it in the sequent
        if (ctx.isFunctionPostVerified(funName))
          funDef.getTemplate
        else
          And(funDef.getPostWoTemplate, funDef.getTemplate)
      } else if (!ctx.isFunctionPostVerified(funName))
        funDef.getPostWoTemplate
      else tru
    (body, assumptions, fullPost)
  }

  def solveParametricVC(assump: Expr, body: Expr, conseq: Expr) = {
    // initialize the constraint tracker
    constTracker.addVC(rootFd, assump, body, conseq)

    var refinementStep: Int = 0
    var toRefineCalls: Option[Set[Call]] = None
    var infRes: Option[InferResult] = None
    do {
      infRes =
        if(ctx.abort)
          Some(InferResult(false, None, List()))
        else{
          Stats.updateCounter(1, "VC-refinement")
          /*
           * uncomment if we want to bound refinements
           * if (refinementStep >= 5)
           * throw new IllegalStateException("Done 4 refinements")
           */
          val refined =
            if (refinementStep >= 1) {
              reporter.info("- More unrollings for invariant inference")

              val toUnrollCalls = if (ctx.targettedUnroll) toRefineCalls else None
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
          if (!refined)
            Some(InferResult(false, None, List()))
          else {
            //solve for the templates in this unroll step
            templateSolver.solveTemplates() match {
              case (Some(model), callsInPath) =>
                toRefineCalls = callsInPath
                //Validate the model here
                instantiateAndValidateModel(model, constTracker.getFuncs)
                Some(InferResult(true, Some(model), constTracker.getFuncs.toList))
              case (None, callsInPath) =>
                toRefineCalls = callsInPath
                //here, we do not know if the template is solvable or not, we need to do more unrollings.
                None
            }
          }
        }
    } while (infRes.isEmpty)
    infRes
  }

  def apply() = {
    if(ctx.abort) {
      Some(InferResult(false, None, List()))
    } else {
      val (body, pre, post) = constructVC(rootFd)
      if (post == tru)
        Some(InferResult(true, Some(Model.empty), List()))
      else
        solveParametricVC(pre, body, post)
    }
  }

  def instantiateModel(model: Model, funcs: Seq[FunDef]) = {
    funcs.collect {
      case fd if fd.hasTemplate =>
        fd -> TemplateInstantiator.instantiateNormTemplates(model, fd.normalizedTemplate.get)
    }.toMap
  }

  def instantiateAndValidateModel(model: Model, funcs: Seq[FunDef]) = {
    val sols = instantiateModel(model, funcs)
    var output = "Invariants for Function: " + rootFd.id + "\n"
    sols foreach {
      case (fd, inv) =>
        val simpInv = simplifyArithmetic(InstUtil.replaceInstruVars(multToTimes(inv), fd))
        reporter.info("- Found inductive invariant: " + fd.id + " --> " + ScalaPrinter(simpInv))
        output += fd.id + " --> " + simpInv + "\n"
    }
    SpecificStats.addOutput(output)

    reporter.info("- Verifying Invariants... ")
    val verifierRes = verifyInvariant(sols)
    val finalRes = verifierRes._1 match {
      case Some(false) =>
        reporter.info("- Invariant verified")
        sols
      case Some(true) =>
        reporter.error("- Invalid invariant, model: " + verifierRes._2.toMap)
        throw new IllegalStateException("")
      case _ =>
        //the solver timed out here
        reporter.error("- Unable to prove or disprove invariant, the invariant is probably true")
        sols
    }
    finalRes
  }

  /**
   * This function creates a new program with each function postcondition strengthened by
   * the inferred postcondition
   */
  def verifyInvariant(newposts: Map[FunDef, Expr]): (Option[Boolean], Model) = {
    val augProg = assignTemplateAndCojoinPost(Map(), program, newposts, uniqueIdDisplay = false)
    //convert the program back to an integer program if necessary
    val newprog =
      if (ctx.usereals) new RealToIntProgram()(augProg)
      else augProg
    val newroot = functionByFullName(fullName(rootFd)(program), newprog).get
    verifyVC(newprog, newroot)
  }

  /**
   * Uses default postcondition VC, but can be overriden in the case of non-standard VCs
   */
  def verifyVC(newprog: Program, newroot: FunDef) = {
    val post = newroot.postcondition.get
    val body = newroot.body.get
    val vc = implies(newroot.precOrTrue, application(post, Seq(body)))
    solveUsingLeon(ctx.leonContext, newprog, VC(vc, newroot, VCKinds.Postcondition))
  }

  import leon.solvers._
  import leon.solvers.unrolling.UnrollingSolver
  def solveUsingLeon(leonctx: LeonContext, p: Program, vc: VC) = {
    val solFactory = SolverFactory.uninterpreted(leonctx, program)
    val smtUnrollZ3 = new UnrollingSolver(ctx.leonContext.toSctx, program, solFactory.getNewSolver()) with TimeoutSolver
    smtUnrollZ3.setTimeout(ctx.vcTimeout * 1000)
    smtUnrollZ3.assertVC(vc)
    smtUnrollZ3.check match {
      case Some(true) =>
        (Some(true), smtUnrollZ3.getModel)
      case r =>
        (r, Model.empty)
    }
  }
}
