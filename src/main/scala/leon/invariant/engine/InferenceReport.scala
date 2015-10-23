/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package invariant.engine

import purescala.Definitions.FunDef
import verification._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Common._
import invariant.templateSolvers._
import invariant.factories._
import invariant.util._
import invariant.structure._
import leon.transformations.InstUtil
import leon.purescala.PrettyPrinter
import Util._
import PredicateUtil._
import ProgramUtil._
import SolverUtil._
import FunctionUtils._
import purescala._

class InferenceCondition(invs: Seq[Expr], funDef: FunDef)
    extends VC(BooleanLiteral(true), funDef, null) {

  var time: Option[Double] = None
  var invariants = invs

  def addInv(invs: Seq[Expr]) {
    invariants ++= invs
  }

  lazy val prettyInv = invariants.map(inv =>
    simplifyArithmetic(InstUtil.replaceInstruVars(multToTimes(inv), fd))) match {
    case Seq() => None
    case invs =>
      invs.map(ExpressionTransformer.simplify _).filter(_ != tru) match {
        case Seq()     => Some(tru)
        case Seq(ninv) => Some(ninv)
        case ninvs     => Some(And(ninvs))
      }
  }

  def status: String = prettyInv match {
    case None => "unknown"
    case Some(inv) =>
      PrettyPrinter(inv)
  }
}

class InferenceReport(fvcs: Map[FunDef, List[VC]], program: Program)(implicit ctx: InferenceContext)
    extends VerificationReport(program, Map()) {

  import scala.math.Ordering.Implicits._
  val conditions: Seq[InferenceCondition] =
    fvcs.flatMap(_._2.map(_.asInstanceOf[InferenceCondition])).toSeq.sortBy(vc => vc.fd.id.name)

  private def infoSep(size: Int): String = "╟" + ("┄" * size) + "╢\n"
  private def infoFooter(size: Int): String = "╚" + ("═" * size) + "╝"
  private def infoHeader(size: Int): String = ". ┌─────────┐\n" +
    "╔═╡ Summary ╞" + ("═" * (size - 12)) + "╗\n" +
    "║ └─────────┘" + (" " * (size - 12)) + "║"

  private def infoLine(str: String, size: Int): String = {
    "║ " + str + (" " * (size - str.size - 2)) + " ║"
  }

  private def fit(str: String, maxLength: Int): String = {
    if (str.length <= maxLength) {
      str
    } else {
      str.substring(0, maxLength - 1) + "…"
    }
  }

  private def funName(fd: FunDef) = InstUtil.userFunctionName(fd)

  override def summaryString: String = if (conditions.size > 0) {
    val maxTempSize = (conditions.map(_.status.size).max + 3)
    val outputStrs = conditions.map(vc => {
      val timeStr = vc.time.map(t => "%-3.3f".format(t)).getOrElse("")
      "%-15s %s %-4s".format(fit(funName(vc.fd), 15), vc.status + (" " * (maxTempSize - vc.status.size)), timeStr)
    })
    val summaryStr = {
      val totalTime = conditions.foldLeft(0.0)((a, ic) => a + ic.time.getOrElse(0.0))
      val inferredConds = conditions.count((ic) => ic.prettyInv.isDefined)
      "total: %-4d  inferred: %-4d  unknown: %-4d  time: %-3.3f".format(
        conditions.size, inferredConds, conditions.size - inferredConds, totalTime)
    }
    val entrySize = (outputStrs :+ summaryStr).map(_.size).max + 2

    infoHeader(entrySize) +
      outputStrs.map(str => infoLine(str, entrySize)).mkString("\n", "\n", "\n") +
      infoSep(entrySize) +
      infoLine(summaryStr, entrySize) + "\n" +
      infoFooter(entrySize)

  } else {
    "No user provided templates were solved."
  }

  def finalProgram: Program = {
    val funToTmpl = conditions.collect {
      case cd if cd.prettyInv.isDefined =>
        cd.fd -> cd.prettyInv.get
    }.toMap
    assignTemplateAndCojoinPost(funToTmpl, program)
  }
}

object InferenceReportUtil {

  /*  def programWoInstrumentation(ctx: InferenceContext, p: Program, ics: Seq[InferenceCondition]) = {
    val funToUninstFun = p.definedFunctions.foldLeft(Map[FunDef, FunDef]()) {
      case (acc, fd) =>
        val uninstFunName = InstUtil.userFunctionName(fd)
        val uninstFdOpt =
          if (uninstFunName.isEmpty) None
          else functionByName(uninstFunName, ctx.initProgram)
        if (uninstFdOpt.isDefined) {
          acc + (fd -> uninstFdOpt.get)
        } else acc
    }
    val funToPost = ics.collect {
      case cd if cd.prettyInv.isDefined && funToUninstFun.contains(cd.fd) =>
        funToUninstFun(cd.fd) -> cd.prettyInv.get
    }.toMap
    //println("Function to template: " + funToTmpl.map { case (k, v) => s"${k.id.name} --> $v" }.mkString("\n"))
    assignTemplateAndCojoinPost(Map(), ctx.initProgram, funToPost, uniqueIdDisplay = false)
  }*/

  def pluginResultInInput(ctx: InferenceContext, ics: Seq[InferenceCondition], p: Program) = {

    val solvedICs = ics.filter { _.prettyInv.isDefined }
    // mapping from init to output
    val outputFunMap =
      functionsWOFields(ctx.initProgram.definedFunctions).map {
        case fd if fd.isTheoryOperation => (fd -> fd)
        case fd => {
          val freshId = FreshIdentifier(fd.id.name, fd.returnType)
          val newfd = new FunDef(freshId, fd.tparams, fd.params, fd.returnType)
          fd -> newfd
        }
      }.toMap

    def fullNameWoInst(fd: FunDef) = {
      val splits = DefOps.fullName(fd)(p).split("-")
      if (!splits.isEmpty) splits(0)
      else ""
    }

    // mapping from p to output
    val progFunMap = (Map[FunDef, FunDef]() /: functionsWOFields(p.definedFunctions)) {
      case (acc, fd) =>
        val inFun = functionByFullName(fullNameWoInst(fd), ctx.initProgram)
        if (inFun.isDefined)
          acc + (fd -> outputFunMap(inFun.get))
        else acc
    }.toMap

    // mapping from init to ic
    val initICmap = (Map[FunDef, InferenceCondition]() /: solvedICs) {
      case (acc, ic) =>
        val initfd = functionByFullName(fullNameWoInst(ic.fd), ctx.initProgram)
        if (initfd.isDefined) {
          acc + (initfd.get -> ic)
        } else acc
    }

    def mapProgram(funMap: Map[FunDef, FunDef]) = {

      def mapExpr(ine: Expr): Expr = {
        val replaced = simplePostTransform((e: Expr) => e match {
          case FunctionInvocation(tfd, args) if funMap.contains(tfd.fd) =>
            FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args)
          case _ => e
        })(ine)
        replaced
      }

      for ((from, to) <- funMap) {
        to.body = from.body.map(mapExpr)
        to.precondition = from.precondition.map(mapExpr)
        if (initICmap.contains(from)) {
          val ic = initICmap(from)
          val paramMap = (ic.fd.params zip from.params).map {
            case (p1, p2) =>
              (p1.id.toVariable -> p2.id.toVariable)
          }.toMap
          val icres = getResId(ic.fd).get
          val npost =
            if (from.hasPostcondition) {
              val resid = getResId(from).get
              val inv = replace(Map(icres.toVariable -> resid.toVariable) ++ paramMap, ic.prettyInv.get)
              val postBody = from.postWoTemplate.map(post => createAnd(Seq(post, inv))).getOrElse(inv)
              Lambda(Seq(ValDef(resid)), postBody)
            } else {
              val resid = FreshIdentifier(icres.name, icres.getType)
              val inv = replace(Map(icres.toVariable -> resid.toVariable) ++ paramMap, ic.prettyInv.get)
              Lambda(Seq(ValDef(resid)), inv)
            }
          to.postcondition = Some(mapExpr(npost))
        } else
          to.postcondition = from.postcondition.map(mapExpr)
        //copy annotations
        from.flags.foreach(to.addFlag(_))
      }
    }
    mapProgram(outputFunMap ++ progFunMap)
    copyProgram(ctx.initProgram, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if outputFunMap.contains(fd) =>
        outputFunMap(fd)
      case d => d
    })
    /*if (debugSimplify)
      println("After Simplifications: \n" + ScalaPrinter.apply(newprog))*/
    //    /newprog
    /*if (ic.prettyInv.isDefined) {
      val uninstFunName = InstUtil.userFunctionName(ic.fd)
      val inputFdOpt =
        if (uninstFunName.isEmpty) None
        else functionByName(uninstFunName, ctx.initProgram)
      inputFdOpt match {
        case None => ctx.initProgram
        case Some(inFd) =>
          ProgramUtil.copyProgram(ctx.initProgram, defs => defs map {
            case fd if fd.id == inFd.id =>
              val newfd = new FunDef(FreshIdentifier(inFd.id.name), inFd.tparams, inFd.params, inFd.returnType)
              newfd.body = inFd.body
              newfd.precondition = inFd.precondition
              val fdres = getResId(ic.fd).get
              val npost =
                if (inFd.hasPostcondition) {
                  val resid = getResId(inFd).get
                  val inv = replace(Map(fdres.toVariable -> resid.toVariable), ic.prettyInv.get)
                  // map also functions here.
                  val postBody = inFd.postWoTemplate.map(post => createAnd(Seq(post, inv))).getOrElse(inv)
                  Lambda(Seq(ValDef(resid)), postBody)
                } else {
                  val resid = FreshIdentifier(fdres.name, fdres.getType)
                  val inv = replace(Map(fdres.toVariable -> resid.toVariable), ic.prettyInv.get)
                  Lambda(Seq(ValDef(resid)), inv)
                }
              newfd.postcondition = Some(npost)
              newfd
            case d => d
          })
      }
    } else ctx.initProgram*/
  }
}