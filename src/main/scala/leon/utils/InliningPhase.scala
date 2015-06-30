/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import leon._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._
import purescala.TypeOps._
import purescala.ExprOps._
import purescala.DefOps._

object InliningPhase extends TransformationPhase {
  
  val name = "Inline @inline functions"
  val description = "Inline functions marked as @inline and remove their definitions"
  
  def apply(ctx: LeonContext, p: Program): Program = {

    def simplifyImplicitClass(e: Expr) = e match {
      case CaseClassSelector(cct, cc: CaseClass, id) =>
        Some(CaseClassSelector(cct, cc, id))

      case _ =>
        None
    }

    def simplify(e: Expr) = {
      fixpoint(postMap(simplifyImplicitClass _))(e)
    }

    for (fd <- p.definedFunctions) {
      fd.fullBody = simplify(preMap {
        case FunctionInvocation(TypedFunDef(fd, tps), args) if fd.flags(IsInlined) =>
          val newBody = replaceFromIDs(fd.params.map(_.id).zip(args).toMap, fd.fullBody)
          Some(instantiateType(newBody, (fd.tparams zip tps).toMap, Map()))
        case _ =>
          None
      }(fd.fullBody))
    }

    filterFunDefs(p, fd => !fd.flags(IsInlined))
  }

}
