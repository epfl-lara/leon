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

object LazinessEliminationPhase extends TransformationPhase {
  val debugLifting = false
  val dumpInputProg = false
  val dumpLiftProg = false
  val dumpProgramWithClosures = true
  val dumpTypeCorrectProg = false
  val dumpProgWithPreAsserts = true
  val dumpProgWOInstSpecs = true
  val dumpInstrumentedProgram = true
  val debugSolvers = false
  val skipStateVerification = false
  val skipResourceVerification = false
  val debugInstVCs = false

  val name = "Laziness Elimination Phase"
  val description = "Coverts a program that uses lazy construct" +
    " to a program that does not use lazy constructs"

  // options that control behavior
  val optRefEquality = LeonFlagOptionDef("refEq", "Uses reference equality for comparing closures", false)
  val optUseOrb = LeonFlagOptionDef("useOrb", "Use Orb to infer constants", false)

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(optUseOrb)

  /**
   * TODO: add inlining annotations for optimization.
   */
  def apply(ctx: LeonContext, prog: Program): Program = {

    if (dumpInputProg)
      println("Input prog: \n" + ScalaPrinter.apply(prog))

    val (pass, msg) = sanityChecks(prog, ctx)
    assert(pass, msg)

    val nprog = liftLazyExpressions(prog)
    if (dumpLiftProg) {
      prettyPrintProgramToFile(nprog, ctx, "-lifted")
    }

    val funsManager = new LazyFunctionsManager(nprog)
    val closureFactory = new LazyClosureFactory(nprog)
    val progWithClosures = (new LazyClosureConverter(nprog, ctx, closureFactory, funsManager)).apply
    if (dumpProgramWithClosures) {
      //println("After closure conversion: \n" + ScalaPrinter.apply(progWithClosures, purescala.PrinterOptions(printUniqueIds = true)))
      prettyPrintProgramToFile(progWithClosures, ctx, "-closures")
    }

    //Rectify type parameters and local types
    val typeCorrectProg = (new TypeRectifier(progWithClosures, closureFactory)).apply
    if (dumpTypeCorrectProg)
      println("After rectifying types: \n" + ScalaPrinter.apply(typeCorrectProg))

    val progWithPre = (new ClosurePreAsserter(typeCorrectProg)).apply
    if (dumpProgWithPreAsserts) {
      //println("After asserting closure preconditions: \n" + ScalaPrinter.apply(progWithPre))
      prettyPrintProgramToFile(progWithPre, ctx, "-withpre", uniqueIds = true)
    }

    // verify the contracts that do not use resources
    val progWOInstSpecs = removeInstrumentationSpecs(progWithPre)
    if (dumpProgWOInstSpecs) {
      //println("After removing instrumentation specs: \n" + ScalaPrinter.apply(progWOInstSpecs))
      prettyPrintProgramToFile(progWOInstSpecs, ctx, "-woinst")
    }
    val checkCtx = contextForChecks(ctx)
    if (!skipStateVerification)
      checkSpecifications(progWOInstSpecs, checkCtx)

    // instrument the program for resources (note: we avoid checking preconditions again here)
    val instrumenter = new LazyInstrumenter(typeCorrectProg, closureFactory)
    val instProg = instrumenter.apply
    if (dumpInstrumentedProgram) {
      //println("After instrumentation: \n" + ScalaPrinter.apply(instProg))
      prettyPrintProgramToFile(instProg, ctx, "-withinst", uniqueIds = true)
    }
    // check specifications (to be moved to a different phase)
    if (!skipResourceVerification)
      checkInstrumentationSpecs(instProg, checkCtx)
    // dump stats
    dumpStats()
    instProg
  }

  /**
   * TODO: enforce that lazy and nested types do not overlap
   * TODO: we are forced to make an assumption that lazy ops takes as type parameters only those
   * type parameters of their return type and not more. (This is checked in the closureFactory,\
   * but may be check this upfront)
   */
  def sanityChecks(p: Program, ctx: LeonContext): (Boolean, String) = {
    // using a bit of a state here
    var failMsg = ""
    val checkres = p.definedFunctions.forall {
      case fd if !fd.isLibrary =>
        /**
         * Fails when the argument to a suspension creation
         * is either a normal or memoized function depending on the flag
         * 'argMem' = true implies fail if the argument is a memoized function
         */
        def failOnClosures(argMem: Boolean, e: Expr) = e match {
          case finv: FunctionInvocation if isLazyInvocation(finv)(p) =>
            finv match {
              case FunctionInvocation(_, Seq(FunctionInvocation(callee, _))) if isMemoized(callee.fd) => argMem
              case _ => !argMem
            }
          case _ => false
        }
        // specs should not create lazy closures, but can refer to memoized functions
        val specCheckFailed = exists(failOnClosures(false, _))(fd.precOrTrue) || exists(failOnClosures(false, _))(fd.postOrTrue)
        if (specCheckFailed) {
          failMsg = "Lazy closure creation in the specification of function: " + fd.id
          false
        } else {
          // cannot suspend a memoized function
          val bodyCheckFailed = exists(failOnClosures(true, _))(fd.body.getOrElse(Util.tru))
          if (bodyCheckFailed) {
            failMsg = "Suspending a memoized function is not supported! in body of:  " + fd.id
            false
          } else {
            def nestedSusp(e: Expr) = e match {
              case finv @ FunctionInvocation(_, Seq(call: FunctionInvocation)) if isLazyInvocation(finv)(p) && isLazyInvocation(call)(p) => true
              case _ => false
            }
            val nestedCheckFailed = exists(nestedSusp)(fd.body.getOrElse(Util.tru))
            if (nestedCheckFailed) {
              failMsg = "Nested suspension creation in the body:  " + fd.id
              false
            } else {
              // arguments or return types of memoized functions cannot be lazy because we do not know how to compare them for equality
              if (isMemoized(fd)) {
                val argCheckFailed = (fd.params.map(_.getType) :+ fd.returnType).exists(LazinessUtil.isLazyType)
                if (argCheckFailed) {
                  failMsg = "Memoized function has a lazy argument or return type: " + fd.id
                  false
                } else true
              } else true
            }
          }
        }
      case _ => true
    }
    (checkres, failMsg)
  }

  /**
   * convert the argument of every lazy constructors to a procedure
   */
  var globalId = 0
  def freshFunctionNameForArg = {
    globalId += 1
    "lazyarg" + globalId
  }

  /**
   * (a) The functions lifts arguments of '$' to functions
   * (b) lifts eager computations to lazy computations if necessary
   * (c) converts memoization to lazy evaluation
   */
  def liftLazyExpressions(prog: Program): Program = {
    var newfuns = Map[ExprStructure, (FunDef, ModuleDef)]()
    val fdmap = prog.definedFunctions.collect {
      case fd if !fd.isLibrary =>
        val nfd = new FunDef(FreshIdentifier(fd.id.name), fd.tparams, fd.params, fd.returnType)
        fd.flags.foreach(nfd.addFlag(_))
        (fd -> nfd)
    }.toMap

    lazy val lazyFun = ProgramUtil.functionByFullName("leon.lazyeval.$.apply", prog).get
    lazy val valueFun = ProgramUtil.functionByFullName("leon.lazyeval.$.value", prog).get

    prog.modules.foreach { md =>
      def exprLifter(inmem: Boolean)(expr: Expr) = expr match {
        // is the arugment of lazy invocation not a function ?
        case finv @ FunctionInvocation(lazytfd, Seq(arg)) if isLazyInvocation(finv)(prog) && !arg.isInstanceOf[FunctionInvocation] =>
          val freevars = variablesOf(arg).toList
          val tparams = freevars.map(_.getType).flatMap(getTypeParameters).distinct
          val argstruc = new ExprStructure(arg)
          val argfun =
            if (newfuns.contains(argstruc)) {
              newfuns(argstruc)._1
            } else {
              //construct type parameters for the function
              // note: we should make the base type of arg as the return type
              val nfun = new FunDef(FreshIdentifier(freshFunctionNameForArg, Untyped, true), tparams map TypeParameterDef.apply,
                freevars.map(ValDef(_)), bestRealType(arg.getType))
              nfun.body = Some(arg)
              newfuns += (argstruc -> (nfun, md))
              nfun
            }
          FunctionInvocation(lazytfd, Seq(FunctionInvocation(TypedFunDef(argfun, tparams),
            freevars.map(_.toVariable))))

        // is the argument of eager invocation not a variable ?
        case finv @ FunctionInvocation(TypedFunDef(fd, _), Seq(arg)) if isEagerInvocation(finv)(prog) && !arg.isInstanceOf[Variable] =>
          val rootType = bestRealType(arg.getType)
          val freshid = FreshIdentifier("t", rootType)
          Let(freshid, arg, FunctionInvocation(TypedFunDef(fd, Seq(rootType)), Seq(freshid.toVariable)))

        case FunctionInvocation(TypedFunDef(fd, targs), args) if isMemoized(fd) && !inmem =>
          // calling a memoized function is modeled as creating a lazy closure and forcing it
          val tfd = TypedFunDef(fdmap.getOrElse(fd, fd), targs)
          val finv = FunctionInvocation(tfd, args)
          // enclose the call within the $ and force it
          val susp = FunctionInvocation(TypedFunDef(lazyFun, Seq(tfd.returnType)), Seq(finv))
          FunctionInvocation(TypedFunDef(valueFun, Seq(tfd.returnType)), Seq(susp))

        case FunctionInvocation(TypedFunDef(fd, targs), args) if fdmap.contains(fd) =>
          FunctionInvocation(TypedFunDef(fdmap(fd), targs), args)
        case e => e
      }
      md.definedFunctions.foreach {
        case fd if fd.hasBody && !fd.isLibrary =>
          def rec(inmem: Boolean)(e: Expr): Expr = e match {
            case Operator(args, op) =>
              val nargs = args map rec(inmem || isMemCons(e)(prog))
              exprLifter(inmem)(op(nargs))
          }
          val nfd = fdmap(fd)
          nfd.fullBody = rec(false)(fd.fullBody)
          /*val nbody = simplePostTransform(exprLifter(false))(fd.body.get)
          val npre = fd.precondition.map(simplePostTransform(exprLifter(true)))
          val npost = fd.postcondition.map(simplePostTransform(exprLifter(true)))*/
          //println(s"New body of $fd: $nbody")
          /*nfd.body = Some(nbody)
          nfd.precondition = npre
          nfd.postcondition = npost*/
        case _ => ;
      }
    }
    val repProg = copyProgram(prog, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef => fdmap.getOrElse(fd, fd)
      case d          => d
    })
    val nprog =
      if (!newfuns.isEmpty) {
        val modToNewDefs = newfuns.values.groupBy(_._2).map { case (k, v) => (k, v.map(_._1)) }.toMap
        appendDefsToModules(repProg, modToNewDefs)
      } else
        repProg
    if (debugLifting)
      println("After lifiting arguments of lazy constructors: \n" + ScalaPrinter.apply(nprog))
    nprog
  }

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

  // cumulative stats
  var totalTime = 0L
  var totalVCs = 0
  var solvedWithZ3 = 0
  var solvedWithCVC4 = 0
  var z3Time = 0L
  var cvc4Time = 0L

  def collectCumulativeStats(rep: VerificationReport) {
    totalTime += rep.totalTime
    totalVCs += rep.totalConditions
    val (withz3, withcvc) = rep.vrs.partition{
      case (vc, vr) =>
        vr.solvedWith.map(s => s.name.contains("smt-z3")).get
    }
    solvedWithZ3 += withz3.size
    solvedWithCVC4 += withcvc.size
    z3Time += withz3.map(_._2.timeMs.getOrElse(0L)).sum
    cvc4Time += withcvc.map(_._2.timeMs.getOrElse(0L)).sum
  }

  def dumpStats() {
    println("totalTime: "+f"${totalTime/1000d}%-3.3f")
    println("totalVCs: "+totalVCs)
    println("solvedWithZ3: "+ solvedWithZ3)
    println("solvedWithCVC4: "+ solvedWithCVC4)
    println("z3Time: "+f"${z3Time/1000d}%-3.3f")
    println("cvc4Time: "+f"${cvc4Time/1000d}%-3.3f")
  }

  def checkSpecifications(prog: Program, checkCtx: LeonContext) {
    // convert 'axiom annotation to library
    prog.definedFunctions.foreach { fd =>
      if (fd.annotations.contains("axiom"))
        fd.addFlag(Annotation("library", Seq()))
    }
    //    val functions = Seq() //Seq("--functions=rotate")
    //    val solverOptions = if (debugSolvers) Seq("--debug=solver") else Seq()
    //    val unfoldFactor = 3 ,
    //        "--unfoldFactor="+unfoldFactor) ++ solverOptions ++ functions
    //val solverOptions = Main.processOptions(Seq("--solvers=smt-cvc4,smt-z3", "--assumepre")
    val report = VerificationPhase.apply(checkCtx, prog)
    // collect stats
    collectCumulativeStats(report)
    println(report.summaryString)
    /*ctx.reporter.whenDebug(leon.utils.DebugSectionTimers) { debug =>
        ctx.timers.outputTable(debug)
      }*/
  }

  def checkInstrumentationSpecs(p: Program, checkCtx: LeonContext) = {
    p.definedFunctions.foreach { fd =>
      if (fd.annotations.contains("axiom"))
        fd.addFlag(Annotation("library", Seq()))
    }
    val funsToCheck = p.definedFunctions.filter(shouldGenerateVC)
    if (checkCtx.findOption(optUseOrb).getOrElse(false)) {
      // create an inference context
      val inferOpts = Main.processOptions(Seq("--disableInfer", "--assumepreInf", "--minbounds"))
      val ctxForInf = LeonContext(checkCtx.reporter, checkCtx.interruptManager,
        inferOpts.options ++ checkCtx.options)
      val inferctx = new InferenceContext(p,  ctxForInf)
      val vcSolver = (funDef: FunDef, prog: Program) => new VCSolver(inferctx, prog, funDef)
      prettyPrintProgramToFile(inferctx.inferProgram, checkCtx, "-inferProg", true)
      (new InferenceEngine(inferctx)).analyseProgram(inferctx.inferProgram, funsToCheck, vcSolver, None)
    } else {
      val vcs = funsToCheck.map { fd =>
        val (ants, post, tmpl) = createVC(fd)
        if (tmpl.isDefined)
          throw new IllegalStateException("Postcondition has holes! Run with --useOrb option")
        val vc = implies(ants, post)
        if (debugInstVCs)
          println(s"VC for function ${fd.id} : " + vc)
        VC(vc, fd, VCKinds.Postcondition)
      }
      val rep = checkVCs(vcs, checkCtx, p)
      // record some stats
      collectCumulativeStats(rep)
      println("Resource Verification Results: \n" + rep.summaryString)
    }
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
  def createVC(fd: FunDef) = {
    val Lambda(Seq(resdef), _) = fd.postcondition.get
    val (pbody, tmpl) = (fd.getPostWoTemplate, fd.template)
    val (instPost, assumptions) = pbody match {
      case And(args) =>
        val (instSpecs, rest) = args.partition(accessesSecondRes(_, resdef.id))
        (createAnd(instSpecs), createAnd(rest))
      case l: Let =>
        val (letsCons, letsBody) = letStarUnapply(l)
        letsBody match {
          case And(args) =>
            val (instSpecs, rest) = args.partition(accessesSecondRes(_, resdef.id))
            (letsCons(createAnd(instSpecs)),
              letsCons(createAnd(rest)))
          case _ =>
            (l, Util.tru)
        }
      case e => (e, Util.tru)
    }
    val ants = createAnd(Seq(fd.precOrTrue, assumptions, Equals(resdef.id.toVariable, fd.body.get)))
    (ants, instPost, tmpl)
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
    override def constructVC(fd: FunDef): (Expr, Expr) = {
      val (ants, post, tmpl) = createVC(fd)
      val conseq = matchToIfThenElse(createAnd(Seq(post, tmpl.getOrElse(Util.tru))))
      (matchToIfThenElse(ants), conseq)
    }

    /**
     * TODO: fix this!!
     */
    override def verifyInvariant(newposts: Map[FunDef, Expr]) = (Some(false), Model.empty)
  }

  /**
   * NOT USED CURRENTLY
   * Lift the specifications on functions to the invariants corresponding
   * case classes.
   * Ideally we should class invariants here, but it is not currently supported
   * so we create a functions that can be assume in the pre and post of functions.
   * TODO: can this be optimized
   */
  /*  def liftSpecsToClosures(opToAdt: Map[FunDef, CaseClassDef]) = {
    val invariants = opToAdt.collect {
      case (fd, ccd) if fd.hasPrecondition =>
        val transFun = (args: Seq[Identifier]) => {
          val argmap: Map[Expr, Expr] = (fd.params.map(_.id.toVariable) zip args.map(_.toVariable)).toMap
          replace(argmap, fd.precondition.get)
        }
        (ccd -> transFun)
    }.toMap
    val absTypes = opToAdt.values.collect {
      case cd if cd.parent.isDefined => cd.parent.get.classDef
    }
    val invFuns = absTypes.collect {
      case abs if abs.knownCCDescendents.exists(invariants.contains) =>
        val absType = AbstractClassType(abs, abs.tparams.map(_.tp))
        val param = ValDef(FreshIdentifier("$this", absType))
        val tparams = abs.tparams
        val invfun = new FunDef(FreshIdentifier(abs.id.name + "$Inv", Untyped),
            tparams, BooleanType, Seq(param))
        (abs -> invfun)
    }.toMap
    // assign bodies for the 'invfuns'
    invFuns.foreach {
      case (abs, fd) =>
        val bodyCases = abs.knownCCDescendents.collect {
          case ccd if invariants.contains(ccd) =>
            val ctype = CaseClassType(ccd, fd.tparams.map(_.tp))
            val cvar = FreshIdentifier("t", ctype)
            val fldids = ctype.fields.map {
              case ValDef(fid, Some(fldtpe)) =>
                FreshIdentifier(fid.name, fldtpe)
            }
            val pattern = CaseClassPattern(Some(cvar), ctype,
              fldids.map(fid => WildcardPattern(Some(fid))))
            val rhsInv = invariants(ccd)(fldids)
            // assert the validity of substructures
            val rhsValids = fldids.flatMap {
              case fid if fid.getType.isInstanceOf[ClassType] =>
                val t = fid.getType.asInstanceOf[ClassType]
                val rootDef = t match {
                  case absT: AbstractClassType => absT.classDef
                  case _ if t.parent.isDefined =>
                    t.parent.get.classDef
                }
                if (invFuns.contains(rootDef)) {
                  List(FunctionInvocation(TypedFunDef(invFuns(rootDef), t.tps),
                    Seq(fid.toVariable)))
                } else
                  List()
              case _ => List()
            }
            val rhs = Util.createAnd(rhsInv +: rhsValids)
            MatchCase(pattern, None, rhs)
        }
        // create a default case
        val defCase = MatchCase(WildcardPattern(None), None, Util.tru)
        val matchExpr = MatchExpr(fd.params.head.id.toVariable, bodyCases :+ defCase)
        fd.body = Some(matchExpr)
    }
    invFuns
  }*/
  // Expressions for testing solvers
  // a test expression
  /*val tparam =
    val dummyFunDef = new FunDef(FreshIdentifier("i"),Seq(), Seq(), IntegerType)
    val eq = Equals(FunctionInvocation(TypedFunDef(dummyFunDef, Seq()), Seq()), InfiniteIntegerLiteral(0))
    import solvers._
    val solver = SimpleSolverAPI(SolverFactory(() => new solvers.smtlib.SMTLIBCVC4Solver(ctx, prog)))
    solver.solveSAT(eq) match {
      case (Some(true), m) =>
        println("Model: "+m.toMap)
      case _ => println("Formula is unsat")
    }
    System.exit(0)*/
}
