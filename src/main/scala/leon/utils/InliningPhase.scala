/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import leon._
import purescala.Definitions._
import purescala.Expressions._
import purescala.TypeOps._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Constructors.caseClassSelector

object InliningPhase extends TransformationPhase {

  val name = "Inline @inline functions"
  val description = "Inline functions marked as @inline and remove their definitions"

  def apply(ctx: LeonContext, p: Program): Program = {

    // Detect inlined functions that are recursive
    val doNotInline = (for (fd <- p.definedFunctions.filter(_.flags(IsInlined)) if p.callGraph.isRecursive(fd)) yield {
      ctx.reporter.warning("Refusing to inline recursive function '"+fd.id.asString(ctx)+"'!")
      fd
    }).toSet

    def doInline(fd: FunDef) = fd.flags(IsInlined) && !doNotInline(fd)

    def simplifyImplicitClass(e: Expr) = e match {
      case CaseClassSelector(cct, cc: CaseClass, id) =>
        Some(caseClassSelector(cct, cc, id))

      case _ =>
        None
    }

    def simplify(e: Expr) = {
      fixpoint(postMap(simplifyImplicitClass))(e)
    }

    for (fd <- p.definedFunctions) {
      fd.fullBody = simplify(preMap ({
        case FunctionInvocation(TypedFunDef(fd, tps), args) if doInline(fd) =>
          val newBody = instantiateType(fd.fullBody, (fd.tparams zip tps).toMap, Map())
          Some(replaceFromIDs(fd.params.map(_.id).zip(args).toMap, newBody))
        case _ =>
          None
      }, applyRec = true)(fd.fullBody))
    }

    filterFunDefs(p, fd => !doInline(fd))
  }

}
