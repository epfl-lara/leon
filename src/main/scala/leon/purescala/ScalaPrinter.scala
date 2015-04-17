/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Constructors._
import Extractors._
import PrinterHelpers._
import Common._
import Expressions._
import Types._
import Definitions._

/** This pretty-printer only print valid scala syntax */
class ScalaPrinter(opts: PrinterOptions, sb: StringBuffer = new StringBuffer) extends PrettyPrinter(opts, sb) {

  override def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = {
   
    tree match {
      case m: ModuleDef =>
        // Don't print synthetic functions
        super.pp(m.copy(defs = m.defs.filter {
          case f:FunDef if f.isSynthetic => false
          case _ => true
        }))
      case Not(Equals(l, r))    => p"$l != $r"
      case Implies(l,r)         => pp(or(not(l), r))
      case Choose(pred, None) => p"choose($pred)"
      case s @ FiniteSet(rss)    => {
        val rs = rss.toSeq
        s.getType match {
          case SetType(ut) =>
            p"Set[$ut]($rs)"
          case _ =>
            p"Set($rs)"
        }
      }
      case m @ FiniteMap(els) => {
        m.getType match {
          case MapType(k,v) =>
            p"Map[$k,$v]($els)"
          case _ =>
            p"Map($els)"
        }
      }
      case ElementOfSet(e,s)    => p"$s.contains(e)"
      case SetUnion(l,r)        => p"$l ++ $r"
      case MapUnion(l,r)        => p"$l ++ $r"
      case SetDifference(l,r)   => p"$l -- $r"
      case SetIntersection(l,r) => p"$l & $r"
      case SetCardinality(s)    => p"$s.size"
      case InfiniteIntegerLiteral(v)        => p"BigInt($v)"

      case a@FiniteArray(elems, oDef, size) => {
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
      }

      case Not(expr)            => p"!$expr"
      case _ =>
        super.pp(tree)
    }
  }
}

object ScalaPrinter extends PrettyPrinterFactory {
  def create(opts: PrinterOptions) = new ScalaPrinter(opts)
}
