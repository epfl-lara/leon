/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Definitions._
import purescala.DefOps.visibleClassDefsFromMain
import purescala.Expressions._

case class CaseClasses(prog: Program) extends SimpleExpressionGrammar {
  def generateSimpleProductions(implicit ctx: LeonContext) = {
    visibleClassDefsFromMain(prog).toSeq.flatMap {
      case acd: AbstractClassDef =>
        val act = acd.typed

        act.knownCCDescendants.map { cct =>
          sGeneric(act.classDef.tparams, act, Seq(cct), _.head, Tags.tagOf(cct))
        }

      case ccd: CaseClassDef =>
        val cct = ccd.typed

        Seq(sGeneric(cct.classDef.tparams, cct, cct.fields.map(_.getType), CaseClass(cct, _), Tags.tagOf(cct)))
    }
  }
}
