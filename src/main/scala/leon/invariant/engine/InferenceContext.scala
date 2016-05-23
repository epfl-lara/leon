/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.engine

import scala.collection.mutable.{ Map => MutableMap }
import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._
import purescala.ExprOps._
import transformations._
import invariant.structure.FunctionUtils._
import invariant.util._
import verification._
import verification.VCKinds
import InferInvariantsPhase._
import ProgramUtil._

/**
 * @author ravi
 */
class InferenceContext(val initProgram: Program, val leonContext: LeonContext) {

  var abort = false // a flag for aborting

  // get  options from ctx or initialize them to default values
  // the following options are enabled by default
  val targettedUnroll = !(leonContext.findOption(optFunctionUnroll).getOrElse(false))
  val autoInference = !(leonContext.findOption(optDisableInfer).getOrElse(false))
  val assumepre = leonContext.findOption(optAssumePre).getOrElse(false)

  // the following options are disabled by default
  val tightBounds = leonContext.findOption(optMinBounds).getOrElse(false)
  val inferTemp = leonContext.findOption(optInferTemp).getOrElse(false)
  val withmult = leonContext.findOption(optWithMult).getOrElse(false)
  val usereals = leonContext.findOption(optUseReals).getOrElse(false)
  val useCegis: Boolean = leonContext.findOption(optCegis).getOrElse(false)
  val dumpStats = leonContext.findOption(GlobalOptions.optBenchmark).getOrElse(false)

  // the following options have default values
  val vcTimeout = leonContext.findOption(optVCTimeout).getOrElse(15L) // in secs
  val nlTimeout = leonContext.findOption(optNLTimeout).getOrElse(15L)
  val totalTimeout = leonContext.findOption(GlobalOptions.optTimeout) // in secs
  val functionsToInfer = leonContext.findOption(GlobalOptions.optFunctions)
  val reporter = leonContext.reporter
  val maxCegisBound = 1000
  val statsSuffix = leonContext.findOption(optStatsSuffix).getOrElse("-stats" + FileCountGUID.getID)

  val instrumentedProg = InstrumentationPhase(leonContext, initProgram)
  // converts qmarks to templates
  val qMarksRemovedProg = {
    val funToTmpl = userLevelFunctions(instrumentedProg).collect {
      case fd if fd.hasTemplate =>
        fd -> fd.getTemplate
    }.toMap
    assignTemplateAndCojoinPost(funToTmpl, instrumentedProg, Map())
  }

  val nlelim = new NonlinearityEliminator(withmult, if (usereals) RealType else IntegerType)

  val inferProgram = {
    // convert nonlinearity to recursive functions
    nlelim(if (usereals) (new IntToRealProgram())(qMarksRemovedProg) else qMarksRemovedProg)
  }

  // other utilities
  lazy val enumerationRelation = {
    // collect strongest relation for enumeration if defined
    var foundStrongest = false
    var rel: (Expr, Expr) => Expr = LessEquals.apply _
    //go over all post-conditions and pick the strongest relation
    instrumentedProg.definedFunctions.foreach((fd) => {
      if (!foundStrongest && fd.hasPostcondition) {
        val cond = fd.postcondition.get
        postTraversal {
          case Equals(_, _) => {
            rel = Equals.apply _
            foundStrongest = true
          }
          case _ => ;
        }(cond)
      }
    })
    rel
  }

  def multOp(e1: Expr, e2: Expr) = {
    FunctionInvocation(TypedFunDef(nlelim.multFun, nlelim.multFun.tparams.map(_.tp)), Seq(e1, e2))
  }

  val validPosts = MutableMap[String, VCResult]()

  /**
   * There should be only one function with funName in the
   * program
   */
  def isFunctionPostVerified(funName: String) = {
    if (validPosts.contains(funName)) {
      validPosts(funName).isValid
    }
    else if (abort) false
    else {
      val verifyPipe = VerificationPhase
      val ctxWithTO = createLeonContext(leonContext, s"--timeout=$vcTimeout", s"--functions=$funName")
      (true /: verifyPipe.run(ctxWithTO, qMarksRemovedProg)._2.results) {
        case (acc, (VC(_, _, vckind), Some(vcRes))) if vcRes.isInvalid =>
          throw new IllegalStateException(s"$vckind invalid for function $funName") // TODO: remove the exception
        case (acc, (VC(_, _, VCKinds.Postcondition), None)) =>
          throw new IllegalStateException(s"Postcondition verification returned unknown for function $funName") // TODO: remove the exception
        case (acc, (VC(_, _, VCKinds.Postcondition), _)) if validPosts.contains(funName) =>
          throw new IllegalStateException(s"Multiple postcondition VCs for function $funName") // TODO: remove the exception
        case (acc, (VC(_, _, VCKinds.Postcondition), Some(vcRes))) =>
          validPosts(funName) = vcRes
          vcRes.isValid
        case (acc, _) => acc
      }
    }
  }
}
