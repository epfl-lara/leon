/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

import leon._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.TypeOps.instantiateType
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Constructors.{caseClassSelector, application}

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

    for (fd <- p.definedFunctions) {
      fd.fullBody = preMap ({
        case FunctionInvocation(tfd, args) if doInline(tfd.fd) =>
          Some(replaceFromIDs((tfd.params.map(_.id) zip args).toMap, tfd.fullBody))

        case CaseClassSelector(cct, cc: CaseClass, id) =>
          Some(caseClassSelector(cct, cc, id))

        case Application(caller: Lambda, args) =>
          Some(application(caller, args))

        case _ =>
          None
      }, applyRec = true)(fd.fullBody)
    }

    filterFunDefs(p, fd => !doInline(fd))
  }

}
