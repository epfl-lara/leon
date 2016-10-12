package leon
package laziness

import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import solvers._
import transformations._
import HOMemUtil._
import purescala.Constructors._
import verification._
import PredicateUtil._
import invariant.engine._

object HOMemVerificationPhase {

  val debugInstVCs = false
  val debugInferProgram = false

  class MemVerificationReport(val stateVerification: Option[VerificationReport],
                              val resourceVeri: Option[VerificationReport],
                              userTmplMap: Map[FunDef, Expr],
                              initProg: Program) {
    val resourceReport = resourceVeri match {
      case Some(inf: InferenceReport) =>
        // create new inference report by pushing the inferred values to the user-level templates.
        val nfvcs = inf.fvcs map {
          case (fd, ics) =>
            // note that the initProg would not have question marks
            val funName = HOMemUtil.userFunctionName(fd)
            val (userFun, tmplInvc) = userTmplMap.find(_._1.id.name == funName).get
            //println("User template: "+userTmpl)
            val nics = if (fd.hasTemplate) {
              ics.map {
                case ic if ic.solved =>
                  val model = ic.invariants.head._2
                  val userInv = tmplInvc match {
                    case FunctionInvocation(_, Seq(Lambda(args, tmplbody))) =>
                      val repmap = args.map { case ValDef(argid) =>
                          val value = model.collectFirst { case (id, value) if id.name == argid.name + "?" => value }.get
                          (argid -> value)
                      }.toMap
                      replaceFromIDs(repmap, tmplbody)
                  }
                  new InferenceCondition(Some((userInv, model)), userFun, ic.time)
                case ic => new InferenceCondition(None, userFun, ic.time)
              }
            } else ics
            (userFun -> nics)
        }
        Some(new InferenceReport(nfvcs, initProg)(inf.ctx))
      case _ => None
    }

    def inferReport = resourceReport match {
      case Some(inf: InferenceReport) => Some(inf)
      case _                          => None
    }
  }

  def removeInstrumentationSpecs(p: Program): Program = {
    def hasInstVar(e: Expr) = {
      exists(InstUtil.instCall(_).isDefined)(e)
    }
    val newPosts = p.definedFunctions.collect {
      case fd if fd.hasTemplate || fd.postcondition.exists { exists(hasInstVar) } =>
        val Lambda(resdef, _) = fd.postcondition.get
        //println(s"postcondition of ${fd.id}: ${fd.postcondition.get}, postWoTemplate: ${fd.postWoTemplate}, tmpl: ${fd.template}")
        val npost = fd.postWoTemplate match {
          case None => Util.tru
          case Some(And(args)) =>
            createAnd(args.filterNot(hasInstVar))
          case Some(l: Let) => // checks if the body of the let can be deconstructed as And
            val (letsCons, letsBody) = letStarUnapply(l)
            //println("Let* body: "+letsBody)
            letsBody match {
              case And(args) =>
                letsCons(createAnd(args.filterNot(hasInstVar)))
              case _ => Util.tru
            }
          case Some(e) =>
            if (hasInstVar(e)) Util.tru
            else e
        }
        (fd -> Lambda(resdef, npost))
    }.toMap
    ProgramUtil.updatePost(newPosts, p) //note: this will not update libraries
  }

  def contextForChecks(userOptions: LeonContext) = {
    val solverOptions = Main.processOptions(Seq("--solvers=orb-smt-cvc4,orb-smt-z3", "--assumepre"))
    LeonContext(userOptions.reporter, userOptions.interruptManager,
      solverOptions.options ++ userOptions.options)
  }

  def collectCumulativeStats(rep: VerificationReport) {
    Stats.updateCumTime(rep.totalTime, "Total-Time")
    Stats.updateCumStats(rep.totalConditions, "Total-VCs-Generated")
    val (withz3, withcvc) = rep.vrs.partition {
      case (vc, vr) =>
        vr.solvedWith.map(s => s.name.contains("orb-smt-z3")).get
    }
    Stats.updateCounter(withz3.size, "Z3SolvedVCs")
    Stats.updateCounter(withcvc.size, "CVC4SolvedVCs")
    Stats.updateCounterStats(withz3.map(_._2.timeMs.getOrElse(0L)).sum, "Z3-Time", "Z3SolvedVCs")
    Stats.updateCounterStats(withcvc.map(_._2.timeMs.getOrElse(0L)).sum, "CVC4-Time", "CVC4SolvedVCs")
  }

  def mapCounterExample(vr: VerificationReport, clFactory: ClosureFactory): VerificationReport = {
    val prog = vr.program
    val nrep = vr.results.map {
      case (vc, Some(vcres)) if vcres.isInvalid =>
        val VCStatus.Invalid(cex) = vcres.status
        val nmodel = new Model(cex.map {
          case (k, v) =>
            val nk =
              if (isStateParam(k))
                FreshIdentifier("cacheKeys", k.getType)
              else k
            (nk -> simplePostTransform {
              case cc @ CaseClass(cct, args) =>
                val cname = cct.classDef.id.name
                clFactory.lambdaOfClosureByName(cname) match {
                  case Some(lam) =>
                    replaceFromIDs((capturedVars(lam) zip args).toMap, lam)
                  case None =>
                    clFactory.memoClasesByName.get(cname) match {
                      case Some(fd) =>
                        FunctionInvocation(TypedFunDef(fd, Seq()), args) // type params are not very important herec
                      case None => cc
                    }
                }
              case e => e
            }(v))
        }.toMap)
        //println("New model: "+nmodel.toMap.map{ case (k,v) => k +" -> "+ v }.mkString("\n"))
        val nstatus = VCStatus.Invalid(nmodel)
        val nres = VCResult(nstatus, vcres.solvedWith, vcres.timeMs)
        (vc -> Some(nres))
      case r => r
    }.toMap
    VerificationReport(prog, nrep)
  }

  // TODO: set a per VC timeout
  def checkSpecifications(clFac: ClosureFactory, prog: Program, checkCtx: LeonContext): VerificationReport = {
    // convert 'axiom annotation to library
    prog.definedFunctions.foreach { fd =>
      if (fd.annotations.contains("axiom"))
        fd.addFlag(Annotation("library", Seq()))
    }
    val report = mapCounterExample(VerificationPhase.apply(checkCtx, prog), clFac)
    // collect stats
    Stats.updateCumTime(report.totalTime, "State-Verification-Time")
    collectCumulativeStats(report)
    if (!checkCtx.findOption(GlobalOptions.optSilent).getOrElse(false)) {
      println(report.summaryString)
    }
    report
  }

  def checkInstrumentationSpecs(clFac: ClosureFactory, p: Program, checkCtx: LeonContext): VerificationReport = {
    p.definedFunctions.foreach { fd =>
      if (fd.annotations.contains("axiom"))
        fd.addFlag(Annotation("library", Seq()))
    }
    val funsToCheck = p.definedFunctions.filter(shouldGenerateVC)
    val useOrb = funsToCheck.exists(_.template.isDefined)
    if (useOrb) {
      val inferctx = getInferenceContext(checkCtx, p)
      val rep = checkUsingOrb(new InferenceEngine(inferctx), inferctx)
      // collect some stats
      Stats.updateCumTime(rep.totalTime, "Resource-Inference-Time")
      Stats.updateCumTime(rep.totalTime, "Total-Time")
      rep
    } else {
      val rep = mapCounterExample(
        checkVCs(funsToCheck.map(vcForFun), checkCtx, p),
        clFac)
      // record some stats
      Stats.updateCumTime(rep.totalTime, "Resource-Verification-Time")
      collectCumulativeStats(rep)
      rep
    }
  }

  def getInferenceContext(checkCtx: LeonContext, p: Program): InferenceContext = {
    // create an inference context
    val inferOpts = Main.processOptions(Seq("--disableInfer", "--assumepreInf", "--minbounds=-100", "--solvers=orb-smt-cvc4"))
    val ctxForInf = LeonContext(checkCtx.reporter, checkCtx.interruptManager,
      inferOpts.options ++ checkCtx.options)
    new InferenceContext(p, ctxForInf)
  }

  def checkUsingOrb(infEngine: InferenceEngine, inferctx: InferenceContext,
                    progressCallback: Option[InferenceCondition => Unit] = None) = {
    if (debugInferProgram) {
      prettyPrintProgramToFile(inferctx.inferProgram, inferctx.leonContext, "-inferProg", true)
    }
    val funsToCheck = inferctx.initProgram.definedFunctions.filter(shouldGenerateVC)
    val vcSolver = (funDef: FunDef, prog: Program) => new VCSolver(inferctx, prog, funDef)
    val results = infEngine.analyseProgram(inferctx.inferProgram,
      funsToCheck.map(InstUtil.userFunctionName), vcSolver, progressCallback)
    new InferenceReport(results.map { case (fd, ic) => (fd -> List(ic)) }, inferctx.inferProgram)(inferctx)
  }

  def accessesSecondRes(e: Expr, resid: Identifier): Boolean =
    exists(_ == TupleSelect(resid.toVariable, 2))(e)

  /**
   * Note: we also skip verification of uninterpreted functions
   */
  def shouldGenerateVC(fd: FunDef) = {
    !fd.isInvariant && !fd.isLibrary && (fd.hasTemplate ||
      (InstUtil.isInstrumented(fd) && fd.hasBody &&
        fd.postcondition.exists { post =>
          val Lambda(Seq(resdef), pbody) = post
          accessesSecondRes(pbody, resdef.id)
        }))
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
    val vctx = new VerificationContext(checkCtx, p, solverF)
    try {
      VerificationPhase.checkVCs(vctx, vcs)
      //println("Resource Verification Results: \n" + veriRep.summaryString)
    } finally {
      solverF.shutdown()
    }
  }

  class VCSolver(ctx: InferenceContext, p: Program, rootFd: FunDef) extends UnfoldingTemplateSolver(ctx, p, rootFd) {

    override def constructVC(fd: FunDef): (Expr, Expr, Expr) = {
      val (body, ants, post, tmpl) = collectAntsPostTmpl(rootFd)
      val conseq = matchToIfThenElse(createAnd(Seq(post, tmpl.getOrElse(Util.tru))))
      //println(s"body: $body ants: $ants conseq: $conseq")
      (matchToIfThenElse(body), matchToIfThenElse(ants), conseq)
    }

    override def verifyVC(newprog: Program, newroot: FunDef) = {
      SolverUtil.solveUsingLeon(contextForChecks(ctx.leonContext), newprog, vcForFun(newroot), ctx.vcTimeout)
    }
  }
}
