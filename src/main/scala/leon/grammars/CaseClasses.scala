/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import leon.purescala.Types.CaseClassType
import purescala.Definitions._
import purescala.DefOps.visibleClassDefsFromMain
import purescala.Expressions.CaseClass

case class CaseClasses(prog: Program) extends SimpleExpressionGrammar {
  def generateSimpleProductions(implicit ctx: LeonContext) = {
    def mkRule(root: ClassDef, cct: CaseClassType) = {
      sGeneric(
        root.tparams, root.typed, cct.fields.map(_.getType), CaseClass(cct, _),
        Tags.tagOf(cct), cost = 1//Math.max(1, cct.fields.size) TODO: Cost = 1 will punish larger constructors
      )
    }

    visibleClassDefsFromMain(prog).toSeq.flatMap {
      case acd: AbstractClassDef =>
        acd.typed.knownCCDescendants map (mkRule(acd, _))

      case ccd: CaseClassDef if ccd.parent.isEmpty =>
        Seq(mkRule(ccd, ccd.typed))

      case _ =>
        Nil
    }
  }
}
