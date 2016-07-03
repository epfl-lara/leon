package leon
package laziness

import invariant.util._

import invariant.structure.FunctionUtils._
import purescala.ScalaPrinter
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import HOMemUtil._
import HOMemVerificationPhase._
import utils._
import java.io._
import invariant.engine.InferenceReport
import transformations._
/**
 * TODO: Function names are assumed to be small case. Fix this!!
 * TODO: pull all ands and ors up so that  there are not nested ands/ors
 */
object HOInferencePhase extends SimpleLeonPhase[Program, MemVerificationReport] {
  val dumpInputProg = false
  val dumpLiftProg = true
  val dumpProgramWithClosures = true
  val dumpTypeCorrectProg = true
  val dumpProgWithPreAsserts = true
  val dumpProgWOInstSpecs = true
  val dumpInstrumentedProgram = true
  val debugSolvers = false
  val skipStateVerification = false
  val skipResourceVerification = false

  val name = "Higher-order Memoization Verification Phase"
  val description = "Coverts a program that uses lazy construct" +
    " to a program that does not use lazy constructs"

  // options that control behavior
  val optRefEquality = LeonFlagOptionDef("refEq", "Uses reference equality for comparing closures", false)

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(optRefEquality)

  def apply(ctx: LeonContext, prog: Program): MemVerificationReport = {
    val (progWOInstSpecs, instProg) = genVerifiablePrograms(ctx, prog)
    val checkCtx = contextForChecks(ctx)
    val stateVeri =
      if (!skipStateVerification)
        Some(checkSpecifications(progWOInstSpecs, checkCtx))
      else None

    val resourceVeri =
      if (!skipResourceVerification)
        Some(checkInstrumentationSpecs(instProg, checkCtx))
      else None
    // dump stats if enabled
    if (ctx.findOption(GlobalOptions.optBenchmark).getOrElse(false)) {
      val modid = prog.units.find(_.isMainUnit).get.id
      val filename = modid + "-stats.txt"
      val pw = new PrintWriter(filename)
      Stats.dumpStats(pw)
      SpecificStats.dumpOutputs(pw)
      ctx.reporter.info("Stats dumped to file: " + filename)
      pw.close()
    }
    // return a report
    new MemVerificationReport(stateVeri, resourceVeri)
  }

  def genVerifiablePrograms(ctx: LeonContext, prog: Program): (Program, Program) = {
    if (dumpInputProg)
      println("Input prog: \n" + ScalaPrinter.apply(prog))

    val (pass, msg) = sanityChecks(prog, ctx)
    assert(pass, msg)

    // refEq is by default false
    val nprog = ExpressionLifter.liftLambdaBody(ctx, prog, ctx.findOption(optRefEquality).getOrElse(false))
    if (dumpLiftProg)
      prettyPrintProgramToFile(nprog, ctx, "-lifted", true)

    val funsManager = new FunctionsManager(nprog)
    val closureFactory = new ClosureFactory(nprog, funsManager)
    val progWithClosures = (new ClosureConverter(nprog, ctx, closureFactory, funsManager)).apply
    if (dumpProgramWithClosures)
      prettyPrintProgramToFile(progWithClosures, ctx, "-closures")

    //Rectify type parameters and local types
    val typeCorrectProg = (new TypeRectifier(progWithClosures, closureFactory)).apply
    if (dumpTypeCorrectProg)
      prettyPrintProgramToFile(typeCorrectProg, ctx, "-typed")
      
    // check termination of all functions
    val termReport =  leon.termination.TerminationPhase(ctx, typeCorrectProg)
    println("Termintion Results: "+termReport.summaryString)    

    val progWithPre = (new ClosurePreAsserter(typeCorrectProg, closureFactory)).apply
    if (dumpProgWithPreAsserts)
      prettyPrintProgramToFile(progWithPre, ctx, "-withpre", uniqueIds = true)

    // verify the contracts that do not use resources
    val progWOInstSpecs = InliningPhase.apply(ctx, removeInstrumentationSpecs(progWithPre))
    if (dumpProgWOInstSpecs)
      prettyPrintProgramToFile(progWOInstSpecs, ctx, "-woinst")

    // instrument the program for resources (note: we avoid checking preconditions again here)
    // Note: do not inline before instrument, because inlining might change the performance properties
    val instrumenter = new MemInstrumenter(typeCorrectProg, ctx, closureFactory, funsManager)
    val instProg = InliningPhase.apply(ctx, instrumenter.apply)
    if (dumpInstrumentedProgram) {
      val runnProg = RunnableCodePhase.apply(ctx, instProg)
      prettyPrintProgramToFile(runnProg, ctx, "-withrun", uniqueIds = true)
      prettyPrintProgramToFile(instProg, ctx, "-withinst", uniqueIds = true)
    }
    (progWOInstSpecs, instProg)
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
              case FunctionInvocation(_, Seq(Lambda(_, FunctionInvocation(callee, _)))) if isMemoized(callee.fd) => argMem
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
              case finv @ FunctionInvocation(_, Seq(Lambda(_, call: FunctionInvocation))) if isLazyInvocation(finv)(p) && isLazyInvocation(call)(p) => true
              case _ => false
            }
            val nestedCheckFailed = exists(nestedSusp)(fd.body.getOrElse(Util.tru))
            if (nestedCheckFailed) {
              failMsg = "Nested suspension creation in the body:  " + fd.id
              false
            } else {
              // arguments or return types of memoized functions cannot be lazy because we do not know how to compare them for equality
              if (hasMemAnnotation(fd)) {
                val argCheckFailed = (fd.params.map(_.getType) :+ fd.returnType).exists(isLazyType)
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
}
