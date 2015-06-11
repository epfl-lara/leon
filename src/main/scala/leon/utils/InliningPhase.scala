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
    val toInline = p.definedFunctions.filter(_.flags(IsInlined)).toSet

    val substs = toInline.map { fd =>
      fd -> { (tps: Seq[TypeTree], s: Seq[Expr]) => 
        val newBody = replaceFromIDs(fd.params.map(_.id).zip(s).toMap, fd.fullBody)
        instantiateType(newBody, (fd.tparams zip tps).toMap, Map())
      }
    }.toMap

    def simplifyImplicitClass(e: Expr) = e match {
      case CaseClassSelector(cct, cc: CaseClass, id) =>
        Some(CaseClassSelector(cct, cc, id))

      case _ =>
        None
    }

    def simplify(e: Expr) = {
      fixpoint(postMap(simplifyImplicitClass _))(e)
    }

    val (np, _) = replaceFunDefs(p)({fd => None}, {(fi, fd) => 
      if (substs contains fd) {
        Some(simplify(substs(fd)(fi.tfd.tps, fi.args)))
      } else {
        None
      }
    })

    removeDefs(np, toInline.map { fd => (fd: Definition) })
  }

}
