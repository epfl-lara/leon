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

object LazinessEliminationPhase extends TransformationPhase {
  val debugLifting = false
  val dumpInputProg = false
  val dumpLiftProg = false
  val dumpProgramWithClosures = true
  val dumpTypeCorrectProg = true
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

  /**
   * TODO: enforce that the specs do not create lazy closures
   * TODO: we are forced to make an assumption that lazy ops takes as type parameters only those
   * type parameters of their return type and not more. (enforce this)
   * TODO: Check that lazy types are not nested
   * TODO: expose in/out state to the user level, so that they can be used in specs
   * For now using lazyinv annotation
   */
  def apply(ctx: LeonContext, prog: Program): Program = {

    if (dumpInputProg)
      println("Input prog: \n" + ScalaPrinter.apply(prog))
    val nprog = liftLazyExpressions(prog)
    if(dumpLiftProg) {
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
    val typeCorrectProg = (new TypeRectifier(progWithClosures, tp => tp.id.name.endsWith("@"))).apply
    if (dumpTypeCorrectProg)
      println("After rectifying types: \n" + ScalaPrinter.apply(typeCorrectProg))
    System.exit(0)

    val progWithPre = (new ClosurePreAsserter(typeCorrectProg, funsManager)).apply
    if (dumpProgWithPreAsserts) {
      //println("After asserting closure preconditions: \n" + ScalaPrinter.apply(progWithPre))
      prettyPrintProgramToFile(progWithPre, ctx, "-withpre")
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
    val instrumenter = new LazyInstrumenter(typeCorrectProg)
    val instProg = instrumenter.apply
    if (dumpInstrumentedProgram) {
      //println("After instrumentation: \n" + ScalaPrinter.apply(instProg))
      prettyPrintProgramToFile(instProg, ctx, "-withinst")
    }
    // check specifications (to be moved to a different phase)
    if (!skipResourceVerification)
      checkInstrumentationSpecs(instProg, checkCtx)
    instProg
  }

  /**
   * convert the argument of every lazy constructors to a procedure
   */
  var globalId = 0
  def freshFunctionNameForArg = {
    globalId += 1
    "lazyarg" + globalId
  }

  def liftLazyExpressions(prog: Program): Program = {
    var newfuns = Map[ExprStructure, (FunDef, ModuleDef)]()
    val fdmap = prog.definedFunctions.collect {
      case fd if !fd.isLibrary =>
        val nfd = new FunDef(FreshIdentifier(fd.id.name), fd.tparams, fd.params, fd.returnType)
        fd.flags.foreach(nfd.addFlag(_))
        (fd -> nfd)
    }.toMap
    prog.modules.foreach { md =>
      md.definedFunctions.foreach {
        case fd if fd.hasBody && !fd.isLibrary =>
          val nbody = simplePostTransform {
            // is the arugment of lazy invocation not a function ?
            case finv @ FunctionInvocation(lazytfd, Seq(arg)) if isLazyInvocation(finv)(prog) && !arg.isInstanceOf[FunctionInvocation] =>
              val freevars = variablesOf(arg).toList
              val tparams = freevars.map(_.getType) flatMap getTypeParameters distinct
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

            case FunctionInvocation(TypedFunDef(fd, targs), args) if fdmap.contains(fd) =>
              FunctionInvocation(TypedFunDef(fdmap(fd), targs), args)
            case e => e

          }(fd.fullBody) // TODO: specs should not create lazy closures. enforce this
          //println(s"New body of $fd: $nbody")
          fdmap(fd).fullBody = nbody
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

  /**
   * Returns a constructor for the let* and also the current
   * body of let*
   */
  def letStarUnapply(e: Expr): (Expr => Expr, Expr) = e match {
      case Let(binder, letv, letb) =>
        val (cons, body) = letStarUnapply(letb)
        (e => Let(binder, letv, cons(e)), letb)
      case base =>
        (e => e, base)
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
          case l : Let =>  // checks if the body of the let can be deconstructed as And
            val (letsCons, letsBody) = letStarUnapply(l)
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
//    val solverOptions = if (debugSolvers) Seq("--debug=solver") else Seq()
//    val ctx = Main.processOptions(Seq("--solvers=smt-cvc4,smt-z3", "--assumepre") ++ solverOptions)

    //(a) create vcs
    // Note: we only need to check specs involving instvars since others were checked before.
    // Moreover, we can add other specs as assumptions since (A => B) ^ ((A ^ B) => C) => A => B ^ C
    //checks if the expression uses res._2 which corresponds to instvars after instrumentation
    def accessesSecondRes(e: Expr, resid: Identifier): Boolean =
        exists(_ == TupleSelect(resid.toVariable, 2))(e)

    val vcs = p.definedFunctions.collect {
      // skipping verification of uninterpreted functions
      case fd if !fd.isLibrary && InstUtil.isInstrumented(fd) && fd.hasBody &&
      fd.postcondition.exists{post =>
        val Lambda(Seq(resdef), pbody) =  post
        accessesSecondRes(pbody, resdef.id)
      } =>
        val Lambda(Seq(resdef), pbody) = fd.postcondition.get
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
        val vc = implies(createAnd(Seq(fd.precOrTrue, assumptions,
            Equals(resdef.id.toVariable, fd.body.get))), instPost)
        if(debugInstVCs)
          println(s"VC for function ${fd.id} : "+vc)
        VC(vc, fd, VCKinds.Postcondition)
    }
    //(b) create a verification context
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
    //(c) check the vcs
    try {
      val veriRep = VerificationPhase.checkVCs(vctx, vcs)
      println("Resource Verification Results: \n" + veriRep.summaryString)
    } finally {
      solverF.shutdown()
    }
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
