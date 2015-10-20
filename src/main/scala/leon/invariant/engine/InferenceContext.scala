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

/**
 * @author ravi
 */
class InferenceContext(
    val initProgram: Program,
    val leonContext: LeonContext,
    val targettedUnroll: Boolean,
    val autoInference: Boolean,
    val dumpStats: Boolean,
    val tightBounds: Boolean,
    val withmult: Boolean,
    val usereals: Boolean,
    val inferTemp: Boolean,
    val useCegis: Boolean,
    val vcTimeout: Int, //in secs
    val maxCegisBound: Int,
    val statsSuffix: String) {

  val reporter = leonContext.reporter
  val functionsToInfer = leonContext.findOption(SharedOptions.optFunctions)
  val totalTimeout = leonContext.findOption(SharedOptions.optTimeout)

  val instrumentedProg = InstrumentationPhase(leonContext, initProgram)
  // convets qmarks to templates
  val qMarksRemovedProg = {
    val funToTmpl = instrumentedProg.definedFunctions.collect {
      case fd if fd.hasTemplate =>
        fd -> fd.getTemplate
    }.toMap
    Util.assignTemplateAndCojoinPost(funToTmpl, instrumentedProg, Map())
  }

  val nlelim = new NonlinearityEliminator(withmult, if (usereals) RealType else IntegerType)

  val inferProgram = {
    // convert nonlinearity to recursive functions
    nlelim(if (usereals)
      (new IntToRealProgram())(qMarksRemovedProg)
    else qMarksRemovedProg)
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
        postTraversal((e) => e match {
          case Equals(_, _) => {
            rel = Equals.apply _
            foundStrongest = true
          }
          case _ => ;
        })(cond)
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
    } else {
      val verifyPipe = VerificationPhase
      val ctxWithTO = Util.createLeonContext(leonContext, s"--timeout=$vcTimeout", s"--functions=$funName")
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
