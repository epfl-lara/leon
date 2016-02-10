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
import LazyVerificationPhase._
import utils._
/**
 * TODO: Function names are assumed to be small case. Fix this!!
 */
object LazinessEliminationPhase extends TransformationPhase {
  val debugLifting = false
  val dumpInputProg = false
  val dumpLiftProg = true
  val dumpProgramWithClosures = true
  val dumpTypeCorrectProg = false
  val dumpProgWithPreAsserts = true
  val dumpProgWOInstSpecs = true
  val dumpInstrumentedProgram = true
  val debugSolvers = false
  val skipStateVerification = true
  val skipResourceVerification = false

  val name = "Laziness Elimination Phase"
  val description = "Coverts a program that uses lazy construct" +
    " to a program that does not use lazy constructs"

  // options that control behavior
  val optRefEquality = LeonFlagOptionDef("refEq", "Uses reference equality for comparing closures", false)
  val optUseOrb = LeonFlagOptionDef("useOrb", "Use Orb to infer constants", false)

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(optUseOrb, optRefEquality)

  /**
   * TODO: add inlining annotations for optimization.
   */
  def apply(ctx: LeonContext, prog: Program): Program = {

    if (dumpInputProg)
      println("Input prog: \n" + ScalaPrinter.apply(prog))

    val (pass, msg) = sanityChecks(prog, ctx)
    assert(pass, msg)

    // refEq is by default false
    val nprog = LazyExpressionLifter.liftLazyExpressions(prog, ctx.findOption(optRefEquality).getOrElse(false))
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

    val progWithPre =  (new ClosurePreAsserter(typeCorrectProg)).apply
    if (dumpProgWithPreAsserts) {
      //println("After asserting closure preconditions: \n" + ScalaPrinter.apply(progWithPre))
      prettyPrintProgramToFile(progWithPre, ctx, "-withpre", uniqueIds = true)
    }

    // verify the contracts that do not use resources
    val progWOInstSpecs = InliningPhase.apply(ctx, removeInstrumentationSpecs(progWithPre))
    if (dumpProgWOInstSpecs) {
      //println("After removing instrumentation specs: \n" + ScalaPrinter.apply(progWOInstSpecs))
      prettyPrintProgramToFile(progWOInstSpecs, ctx, "-woinst")
    }
    val checkCtx = contextForChecks(ctx)
    if (!skipStateVerification)
      checkSpecifications(progWOInstSpecs, checkCtx)

    // instrument the program for resources (note: we avoid checking preconditions again here)
    val instrumenter = new LazyInstrumenter(InliningPhase.apply(ctx, typeCorrectProg), closureFactory)
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
}
