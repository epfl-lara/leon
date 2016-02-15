package leon
package laziness

import invariant.factories._
import invariant.util.Util._
import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Extractors._
import purescala.Types._
import purescala.TypeOps._
import leon.invariant.util.TypeUtil._
import leon.invariant.util.LetTupleSimplification._
import leon.verification.VerificationPhase
import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter
import scala.util.matching.Regex
import leon.purescala.PrettyPrinter
import leon.solvers._
import leon.solvers.z3._
import leon.transformations._
import leon.LeonContext
import leon.LeonOptionDef
import leon.Main
import leon.TransformationPhase
import LazinessUtil._
import invariant.datastructure._
import invariant.util.ProgramUtil._
import purescala.Constructors._
import leon.verification._
import PredicateUtil._
import leon.invariant.engine._

object LazyVerificationPhase {

  val debugInstVCs = false
  val debugInferProgram = true

  def removeInstrumentationSpecs(p: Program): Program = {
    def hasInstVar(e: Expr) = {
      exists { e => InstUtil.InstTypes.exists(i => i.isInstVariable(e)) }(e)
    }
    val newPosts = p.definedFunctions.collect {
      case fd if fd.postcondition.exists { exists(hasInstVar) } =>
        // remove the conjuncts that use instrumentation vars
        val Lambda(resdef, pbody) = fd.postcondition.get
        val npost = pbody match {
          case And(args) =>
            createAnd(args.filterNot(hasInstVar))
          case l: Let => // checks if the body of the let can be deconstructed as And
            //println(s"Fist let val: ${l.value} body: ${l.body}")
            val (letsCons, letsBody) = letStarUnapply(l)
            //println("Let* body: "+letsBody)
            letsBody match {
              case And(args) =>
                letsCons(createAnd(args.filterNot(hasInstVar)))
              case _ => Util.tru
            }
          case e => Util.tru
        }
        (fd -> Lambda(resdef, npost))
    }.toMap
    ProgramUtil.updatePost(newPosts, p) //note: this will not update libraries
  }

  def contextForChecks(userOptions: LeonContext) = {
    val solverOptions = Main.processOptions(Seq("--solvers=smt-cvc4,smt-z3", "--assumepre"))
    LeonContext(userOptions.reporter, userOptions.interruptManager,
      solverOptions.options ++ userOptions.options)
  }

  def collectCumulativeStats(rep: VerificationReport) {
    Stats.updateCumTime(rep.totalTime, "Total-Verification-Time")
    Stats.updateCumStats(rep.totalConditions, "Total-VCs-Generated")
    val (withz3, withcvc) = rep.vrs.partition {
      case (vc, vr) =>
        vr.solvedWith.map(s => s.name.contains("smt-z3")).get
    }
    Stats.updateCounter(withz3.size, "Z3SolvedVCs")
    Stats.updateCounter(withcvc.size, "CVC4SolvedVCs")
    Stats.updateCounterStats(withz3.map(_._2.timeMs.getOrElse(0L)).sum, "Z3-Time", "Z3SolvedVCs")
    Stats.updateCounterStats(withcvc.map(_._2.timeMs.getOrElse(0L)).sum, "CVC4-Time", "CVC4SolvedVCs")
  }

  def checkSpecifications(prog: Program, checkCtx: LeonContext) {
    // convert 'axiom annotation to library
    prog.definedFunctions.foreach { fd =>
      if (fd.annotations.contains("axiom"))
        fd.addFlag(Annotation("library", Seq()))
    }
    val report = VerificationPhase.apply(checkCtx, prog)
    // collect stats
    collectCumulativeStats(report)
    println(report.summaryString)
  }

  def checkInstrumentationSpecs(p: Program, checkCtx: LeonContext, useOrb: Boolean) = {
    p.definedFunctions.foreach { fd =>
      if (fd.annotations.contains("axiom"))
        fd.addFlag(Annotation("library", Seq()))
    }
    val funsToCheck = p.definedFunctions.filter(shouldGenerateVC)
    val rep =
      if (useOrb) {
        // create an inference context
        val inferOpts = Main.processOptions(Seq("--disableInfer", "--assumepreInf", "--minbounds", "--solvers=smt-cvc4"))
        val ctxForInf = LeonContext(checkCtx.reporter, checkCtx.interruptManager,
          inferOpts.options ++ checkCtx.options)
        val inferctx = new InferenceContext(p, ctxForInf)
        val vcSolver = (funDef: FunDef, prog: Program) => new VCSolver(inferctx, prog, funDef)

        if (debugInferProgram)
          prettyPrintProgramToFile(inferctx.inferProgram, checkCtx, "-inferProg", true)

        val results = (new InferenceEngine(inferctx)).analyseProgram(inferctx.inferProgram, 
            funsToCheck.map(InstUtil.userFunctionName), vcSolver, None)
        new InferenceReport(results.map { case (fd, ic) => (fd -> List[VC](ic)) }, inferctx.inferProgram)(inferctx)
      } else {
        val rep = checkVCs(funsToCheck.map(vcForFun), checkCtx, p)
        // record some stats
        collectCumulativeStats(rep)
        rep
      }
    println("Resource Verification Results: \n" + rep.summaryString)
  }

  def accessesSecondRes(e: Expr, resid: Identifier): Boolean =
      exists(_ == TupleSelect(resid.toVariable, 2))(e)

  /**
   * Note: we also skip verification of uninterpreted functions
   */
  def shouldGenerateVC(fd: FunDef) = {
    !fd.isLibrary && InstUtil.isInstrumented(fd) && fd.hasBody &&
      fd.postcondition.exists { post =>
        val Lambda(Seq(resdef), pbody) = post
        accessesSecondRes(pbody, resdef.id)
      }
  }

  /**
   * creates vcs
   *  Note: we only need to check specs involving instvars since others were checked before.
   *  Moreover, we can add other specs as assumptions since (A => B) ^ ((A ^ B) => C) => A => B ^ C
   *  checks if the expression uses res._2 which corresponds to instvars after instrumentation
   */
  def vcForFun(fd: FunDef) = {
    val (body, ants, post, tmpl) = collectAntsPostTmpl(fd)
    if (tmpl.isDefined)
      throw new IllegalStateException("Postcondition has holes! Run with --useOrb option")
    val vc = implies(And(ants, body), post)
    if (debugInstVCs)
      println(s"VC for function ${fd.id} : " + vc)
    VC(vc, fd, VCKinds.Postcondition)
  }

  def collectAntsPostTmpl(fd: FunDef) = {
    val Lambda(Seq(resdef), _) = fd.postcondition.get
    val (pbody, tmpl) = (fd.getPostWoTemplate, fd.template)
    val (instPost, assumptions) = pbody match {
      case And(args) =>
        val (instSpecs, rest) = args.partition(accessesSecondRes(_, resdef.id))
        (createAnd(instSpecs), createAnd(rest))
      case l: Let =>
        val (letsCons, letsBody) = letStarUnapplyWithSimplify(l)
        letsBody match {
          case And(args) =>
            val (instSpecs, rest) = args.partition(accessesSecondRes(_, resdef.id))
            (letsCons(createAnd(instSpecs)), letsCons(createAnd(rest)))
          case _ =>
            (l, Util.tru)
        }
      case e => (e, Util.tru)
    }
    val ants =
      if (fd.usePost) createAnd(Seq(fd.precOrTrue, assumptions))
      else fd.precOrTrue
    (Equals(resdef.id.toVariable, fd.body.get), ants, instPost, tmpl)
  }

  def checkVCs(vcs: List[VC], checkCtx: LeonContext, p: Program) = {
    val timeout: Option[Long] = None
    val reporter = checkCtx.reporter
    // Solvers selection and validation
    val baseSolverF = SolverFactory.getFromSettings(checkCtx, p)
    val solverF = timeout match {
      case Some(sec) =>
        baseSolverF.withTimeout(sec / 1000)
      case None =>
        baseSolverF
    }
    val vctx = VerificationContext(checkCtx, p, solverF, reporter)
    try {
      VerificationPhase.checkVCs(vctx, vcs)
      //println("Resource Verification Results: \n" + veriRep.summaryString)
    } finally {
      solverF.shutdown()
    }
  }

  class VCSolver(ctx: InferenceContext, p: Program, rootFd: FunDef) extends
  	UnfoldingTemplateSolver(ctx, p, rootFd) {

    override def constructVC(fd: FunDef): (Expr, Expr, Expr) = {
      val (body, ants, post, tmpl) = collectAntsPostTmpl(rootFd)
      val conseq = matchToIfThenElse(createAnd(Seq(post, tmpl.getOrElse(Util.tru))))
      //println(s"body: $body ants: $ants conseq: $conseq")
      (matchToIfThenElse(body), matchToIfThenElse(ants), conseq)
    }

    override def verifyVC(newprog: Program, newroot: FunDef) = {
      solveUsingLeon(contextForChecks(ctx.leonContext), newprog, vcForFun(newroot))
    }
  }
}
