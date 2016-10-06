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
import leon.solvers.SolverFactory

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
  val tightBounds = leonContext.findOption(optMinBounds)
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
  val webMode = leonContext.findOptionOrDefault(optWebMode)

  val instrumentedProg = InstrumentationPhase(leonContext, initProgram)
  // converts qmarks to templates and make all template variables have real type
  val (qMarksRemovedProg, progWOTemplate) = {
    val funToTmpl = userLevelFunctions(instrumentedProg).collect {
      case fd if fd.hasTemplate =>
        fd -> fd.getTemplate
    }.toMap
    (assignTemplateAndCojoinPost(funToTmpl, instrumentedProg, Map()),
      assignTemplateAndCojoinPost(Map(), instrumentedProg, Map()))
  }

  val nlelim = new NonlinearityEliminator(withmult, if (usereals) RealType else IntegerType)

  val inferProgram = {
    // convert nonlinearity to recursive functions
    nlelim(if (usereals) (new IntToRealProgram())(qMarksRemovedProg) else qMarksRemovedProg)
  }
  //println("Infer Program: "+purescala.ScalaPrinter(inferProgram))

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

  val validPosts = MutableMap[String, Boolean]()
  val userLevelFunctionsMap = ProgramUtil.userLevelFunctions(progWOTemplate).map { fd =>
    purescala.DefOps.fullName(fd)(progWOTemplate) -> fd
  }.toMap

  /**
   * There should be only one function with funName in the
   * program
   */
  def isFunctionPostVerified(funName: String) = {
    if (validPosts.contains(funName)) validPosts(funName)
    else if (abort) false
    else {
      val vctx = new VerificationContext(leonContext, progWOTemplate,
        SolverFactory.getFromSettings(leonContext, progWOTemplate))
      val vcs = (new DefaultTactic(vctx)).generateVCs(userLevelFunctionsMap(funName))
      (true /: vcs) { (acc, vc) =>
        SolverUtil.solveUsingLeon(leonContext, progWOTemplate, vc, vcTimeout) match {
          case (Some(true), _) =>
            leonContext.reporter.fatalError(s"${vc.kind} invalid for function $funName")
          case (None, _) if vc.kind == VCKinds.Postcondition =>
            validPosts.update(funName, false)
            false
          case (None, _) =>
            leonContext.reporter.fatalError(s"${vc.kind} verification returned unknown for function $funName")
          case (Some(false), _) if vc.kind == VCKinds.Postcondition =>
            validPosts.update(funName, true)
            true
          case _ => acc // here, we have verified a VC that is not post, so skip it
        }
      }
    }
  }
}
