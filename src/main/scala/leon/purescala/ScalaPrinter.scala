/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Extractors._
import PrinterHelpers._
import Common._
import Expressions._
import Types._
import Definitions._
import org.apache.commons.lang3.StringEscapeUtils

/** This pretty-printer only print valid scala syntax */
class ScalaPrinter(opts: PrinterOptions,
                   opgm: Option[Program],
                   sb: StringBuffer = new StringBuffer) extends PrettyPrinter(opts, opgm, sb) {

  private val dbquote = "\""
  override def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = {

    tree match {
      case m: ModuleDef =>
        // Don't print synthetic functions
        super.pp(m.copy(defs = m.defs.filter {
          case f: FunDef if f.isSynthetic => false
          case _ => true
        }))
      case Not(Equals(l, r))         => optP { p"$l != $r" }
      case Choose(pred)              => p"choose($pred)"

      case s @ FiniteSet(rss, t)     => p"Set[$t](${rss.toSeq})"
      case ElementOfSet(e,s)         => p"$s.contains($e)"
      case SetUnion(l,r)             => optP { p"$l ++ $r" }
      case SetDifference(l,r)        => optP { p"$l -- $r" }
      case SetIntersection(l,r)      => optP { p"$l & $r" }
      case SetCardinality(s)         => p"$s.size"
      case SubsetOf(subset,superset) => p"$subset.subsetOf($superset)"

      case MapUnion(l,r)             => optP { p"$l ++ $r" }
      case m @ FiniteMap(els, k, v)  => p"Map[$k,$v]($els)"

      case InfiniteIntegerLiteral(v) => p"BigInt($v)"
      case StringLiteral(v) =>
        if(v.count(c => c == '\n') >= 1 && v.length >= 80 && v.indexOf("\"\"\"") == -1) {
          p"$dbquote$dbquote$dbquote$v$dbquote$dbquote$dbquote"
        } else {
          val escaped = StringEscapeUtils.escapeJava(v)
          p"$dbquote$escaped$dbquote"
        }

      case a@FiniteArray(elems, oDef, size) =>
        import ExprOps._
        val ArrayType(underlying) = a.getType
        val default = oDef.getOrElse(simplestValue(underlying))
        size match {
          case IntLiteral(s) => {
            val explicitArray = Array.fill(s)(default)
            for((id, el) <- elems)
              explicitArray(id) = el
            val lit = explicitArray.toList
            p"Array($lit)"
          }
          case size => {
            p"""|{
                |  val tmp = Array.fill($size)($default)
                |"""
            for((id, el) <- elems)
              p""""|  tmp($id) = $el
                   |"""
            p"""|  tmp
                |}"""

          }
        }

      case Not(expr) => p"!$expr"
      case Forall(args, bd) =>
        p"""|forall(($args) =>
            |  $bd
            |)"""
      case NoTree(tpe) =>
        p"(_ : $tpe)"
      case _ =>
        super.pp(tree)
    }
  }
}

object ScalaPrinter extends PrettyPrinterFactory {
  def create(opts: PrinterOptions, opgm: Option[Program]) = new ScalaPrinter(opts, opgm)
}
