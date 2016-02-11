package leon
package invariant.templateSolvers

import scala.collection.mutable.{Map => MutableMap}
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import java.io._
import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.structure._
import invariant.structure.FunctionUtils._
import leon.solvers.Model
import PredicateUtil._
import ExpressionTransformer._

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

  /**
   * Completes a model by adding mapping to new template variables
   */
  def completeModel(model: Model, ids: Set[Identifier]) = {
    val idmap = ids.map((id) => {
      if (!model.isDefinedAt(id)) {
        (id, simplestValue(id.getType))
      } else (id, model(id))
    }).toMap
    new Model(idmap)
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

  var vcCache = Map[FunDef, Expr]()
  protected def getVCForFun(fd: FunDef): Expr = {
    vcCache.getOrElse(fd, {
      val vcInit = ctrTracker.getVC(fd).toExpr
      val vc = if (ctx.usereals)
        ExpressionTransformer.IntLiteralToReal(vcInit)
      else vcInit
      vcCache += (fd -> vc)
      vc
    })
  }

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  def solveTemplates(): (Option[Model], Option[Set[Call]]) = {
    val funcs = ctrTracker.getFuncs
    val tempIds = funcs.flatMap { fd =>
      val vc = ctrTracker.getVC(fd)
      if (dumpVCtoConsole || dumpVCasText) {
        val filename = "vc-" + FileCountGUID.getID
        if (dumpVCtoConsole) {
          println("Func: " + fd.id + " VC: " + vc)
        }
        if (dumpVCasText) {
          val wr = new PrintWriter(new File(filename + ".txt"))
          println("Printed VC of " + fd.id + " to file: " + filename)
          wr.println(vc.toString())
          wr.close()
        }
      }
      if (ctx.dumpStats) {
        Stats.updateCounterStats(vc.atomsCount, "VC-size", "VC-refinement")
        Stats.updateCounterStats(vc.funsCount, "UIF+ADT", "VC-refinement")
      }
      vc.templateIdsInFormula
    }.toSet

    Stats.updateCounterStats(tempIds.size, "TemplateIds", "VC-refinement")
    if (ctx.abort) (None, None)
    else solve(tempIds, funcs)
  }

  def solve(tempIds: Set[Identifier], funcVCs: Seq[FunDef]): (Option[Model], Option[Set[Call]])
}