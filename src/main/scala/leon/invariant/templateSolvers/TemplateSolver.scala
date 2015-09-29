package leon
package invariant.templateSolvers

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import leon.invariant._
import scala.util.control.Breaks._
import scala.concurrent._
import scala.concurrent.duration._
import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.structure._
import invariant.structure.FunctionUtils._
import leon.solvers.Model

abstract class TemplateSolver(ctx: InferenceContext, val rootFun: FunDef,
  ctrTracker: ConstraintTracker) {

  protected val reporter = ctx.reporter
  //protected val cg = CallGraphUtil.constructCallGraph(program)

  //some constants
  protected val fls = BooleanLiteral(false)
  protected val tru = BooleanLiteral(true)
  //protected val zero = IntLiteral(0)

  private val dumpVCtoConsole = false
  private val dumpVCasText = false
  private val dumpVCasSMTLIB = false

  /**
   * Completes a model by adding mapping to new template variables
   */
  def completeModel(model: Map[Identifier, Expr], tempIds: Set[Identifier]): Map[Identifier, Expr] = {
    tempIds.map((id) => {
      if (!model.contains(id)) {
        (id, simplestValue(id.getType))
      } else (id, model(id))
    }).toMap
  }

  /**
   * Computes the invariant for all the procedures given a mapping for the
   * template variables.
   */
  def getAllInvariants(model: Model): Map[FunDef, Expr] = {
    val templates = ctrTracker.getFuncs.collect {
      case fd if fd.hasTemplate =>
        fd -> fd.getTemplate
    }
    TemplateInstantiator.getAllInvariants(model, templates.toMap)
  }

  protected def getVCForFun(fd: FunDef): Expr = {
    ctrTracker.getVC(fd).toExpr
  }

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  def solveTemplates(): (Option[Model], Option[Set[Call]]) = {
    //traverse each of the functions and collect the VCs
    val funcs = ctrTracker.getFuncs
    val funcExprs = funcs.map((fd) => {
      val vc = if (ctx.usereals)
        ExpressionTransformer.IntLiteralToReal(getVCForFun(fd))
      else getVCForFun(fd)
      if (dumpVCtoConsole || dumpVCasText || dumpVCasSMTLIB) {
        //val simpForm = simplifyArithmetic(vc)
        val filename = "vc-" + FileCountGUID.getID
        if (dumpVCtoConsole) {
          println("Func: " + fd.id + " VC: " + vc)
        }
        if (dumpVCasText) {
          val wr = new PrintWriter(new File(filename + ".txt"))
          //ExpressionTransformer.PrintWithIndentation(wr, vcstr)
          println("Printed VC of " + fd.id + " to file: " + filename)
          wr.println(vc.toString)
          wr.flush()
          wr.close()
        }
        if (dumpVCasSMTLIB) {
          Util.toZ3SMTLIB(vc, filename + ".smt2", "QF_LIA", ctx.leonContext, ctx.program)
          println("Printed VC of " + fd.id + " to file: " + filename)
        }
      }

      if (ctx.dumpStats) {
        Stats.updateCounterStats(Util.atomNum(vc), "VC-size", "VC-refinement")
        Stats.updateCounterStats(Util.numUIFADT(vc), "UIF+ADT", "VC-refinement")
      }
      (fd -> vc)
    }).toMap
    //Assign some values for the template variables at random (actually use the simplest value for the type)
    val tempIds = funcExprs.foldLeft(Set[Identifier]()) {
      case (acc, (_, vc)) =>
        //val tempOption = if (fd.hasTemplate) Some(fd.getTemplate) else None
        //if (!tempOption.isDefined) acc
        //else
        acc ++ Util.getTemplateIds(vc)
    }

    Stats.updateCounterStats(tempIds.size, "TemplateIds", "VC-refinement")
    val solution = solve(tempIds, funcExprs)
    solution
  }

  def solve(tempIds: Set[Identifier], funcVCs: Map[FunDef, Expr]): (Option[Model], Option[Set[Call]])
}