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

    def trivialPost(fd: FunDef) = fd.postcondition match {
      case None                                  => true
      case Some(Lambda(_, BooleanLiteral(true))) => true
      case _                                     => false
    }
    // Detect inlined functions that are recursive
    val doNotInline = p.definedFunctions.filter(fd => fd.flags(IsInlined)).collect {
      case fd if p.callGraph.isRecursive(fd) =>
        ctx.reporter.warning("Refusing to inline recursive function '" + fd.id.asString(ctx) + "'!")
        fd
      case fd if !trivialPost(fd) || fd.precOrTrue != BooleanLiteral(true) =>
        ctx.reporter.warning("Refusing to inline function with non-trivial contracts '" + fd.id.asString(ctx) + "'!")
        fd
      case fd if !fd.hasBody =>
        ctx.reporter.warning("Refusing to inline function bodyless function '" + fd.id.asString(ctx) + "'!")
    }.toSet

    def doInline(fd: FunDef) = fd.flags(IsInlined) && !doNotInline(fd)

    for (fd <- p.definedFunctions) {
      fd.fullBody = preMap ({
        case FunctionInvocation(tfd, args) if doInline(tfd.fd) =>
          Some(replaceFromIDs((tfd.params.map(_.id) zip args).toMap, tfd.body.get))

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
