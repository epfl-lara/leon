/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.engine

import purescala.Definitions.FunDef
import verification._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Common._
import invariant.util._
import invariant.structure._
import leon.transformations.InstUtil
import leon.purescala.PrettyPrinter
import Util._
import PredicateUtil._
import ProgramUtil._
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
    "║ " + str + (" " * (size - str.length - 2)) + " ║"
  }

  private def fit(str: String, maxLength: Int): String = {
    if (str.length <= maxLength) {
      str
    } else {
      str.substring(0, maxLength - 1) + "…"
    }
  }

  private def funName(fd: FunDef) = InstUtil.userFunctionName(fd)

  override def summaryString: String = if (conditions.nonEmpty) {
    val maxTempSize = (conditions.map(_.status.length).max + 3)
    val outputStrs = conditions.map(vc => {
      val timeStr = vc.time.map(t => "%-3.3f".format(t)).getOrElse("")
      "%-15s %s %-4s".format(fit(funName(vc.fd), 15), vc.status + (" " * (maxTempSize - vc.status.length)), timeStr)
    })
    val summaryStr = {
      val totalTime = conditions.foldLeft(0.0)((a, ic) => a + ic.time.getOrElse(0.0))
      val inferredConds = conditions.count((ic) => ic.prettyInv.isDefined)
      "total: %-4d  inferred: %-4d  unknown: %-4d  time: %-3.3f".format(
        conditions.size, inferredConds, conditions.size - inferredConds, totalTime)
    }
    val entrySize = (outputStrs :+ summaryStr).map(_.length).max + 2

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

  def pushResultsToInput(ctx: InferenceContext, ics: Seq[InferenceCondition]) = {

    val initFuns = functionsWOFields(ctx.initProgram.definedFunctions).filter { fd =>
      !fd.isTheoryOperation && !fd.annotations.contains("library")
    }
    val solvedICs = ics.filter { _.prettyInv.isDefined }

    // mapping from init to output
    val initToOutput =
      initFuns.map { fd =>
        val freshId = FreshIdentifier(fd.id.name, fd.returnType)
        val newfd = new FunDef(freshId, fd.tparams, fd.params, fd.returnType)
        fd -> newfd
      }.toMap

    def fullNameWoInst(fd: FunDef) = {
      val splits = DefOps.fullName(fd)(ctx.inferProgram).split("-")
      if (splits.nonEmpty) splits(0)
      else ""
    }

    val nameToInitFun = initFuns.map { fd =>
      DefOps.fullName(fd)(ctx.initProgram) -> fd
    }.toMap

    // mapping from init to ic
    val initICMap = (Map[FunDef, InferenceCondition]() /: solvedICs) {
      case (acc, ic) =>
        nameToInitFun.get(fullNameWoInst(ic.fd)) match {
          case Some(initfd) =>
            acc + (initfd -> ic)
          case _ => acc
        }
    }

    def mapExpr(ine: Expr): Expr = {
      val replaced = simplePostTransform {
        case e@FunctionInvocation(TypedFunDef(fd, targs), args) =>
          if (initToOutput.contains(fd)) {
            FunctionInvocation(TypedFunDef(initToOutput(fd), targs), args)
          } else {
            nameToInitFun.get(fullNameWoInst(fd)) match {
              case Some(ifun) if initToOutput.contains(ifun) =>
                FunctionInvocation(TypedFunDef(initToOutput(ifun), targs), args)
              case _ => e
            }
          }
        case e => e
      }(ine)
      replaced
    }
    // copy bodies and specs
    for ((from, to) <- initToOutput) {
      to.body = from.body.map(mapExpr)
      to.precondition = from.precondition.map(mapExpr)
      val icOpt = initICMap.get(from)
      if (icOpt.isDefined) {
        val ic = icOpt.get
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

    copyProgram(ctx.initProgram, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if initToOutput.contains(fd) =>
        initToOutput(fd)
      case d => d
    })
  }
}