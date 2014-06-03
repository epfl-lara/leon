/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package smtlib

import utils._
import purescala._
import Common._
import Trees._
import Extractors._
import TypeTrees._

import _root_.smtlib.sexpr.SExprs._
import _root_.smtlib.interpreters.CVC4Interpreter
import _root_.smtlib.Commands.{Identifier => _, _}

trait SMTLIBCVC4Target extends SMTLIBTarget {
  this: SMTLIBSolver =>

  def targetName = "cvc4"

  def getNewInterpreter() = new CVC4Interpreter

  override def declareSort(t: TypeTree): SExpr = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case TypeParameter(id) =>
          val s = id2sym(id)
          val cmd = NonStandardCommand(SList(SSymbol("declare-sort"), s, SInt(0)))
          sendCommand(cmd)
          s
        case SetType(base) =>
          SList(SSymbol("Set"), declareSort(base))
        case _ =>
          super[SMTLIBTarget].declareSort(t)
      }
    }
  }

  override def fromSMT(s: SExpr, tpe: TypeTree)(implicit letDefs: Map[SSymbol, SExpr]): Expr = (s, tpe) match {
    case (s: SSymbol, tp: TypeParameter) =>
      val n = s.s.split("_").toList.last
      GenericValue(tp, n.toInt)

    case (SList(SSymbol("as") ::  SSymbol("emptyset") :: _), SetType(base)) =>
      FiniteSet(Seq()).setType(tpe)

    case (SList(SSymbol("setenum") :: elems), SetType(base)) =>
      FiniteSet(elems.map(fromSMT(_, base))).setType(tpe)

    case (SList(SSymbol("union") :: elems), SetType(base)) =>
      FiniteSet(elems.map(fromSMT(_, tpe) match {
        case FiniteSet(elems) => elems
      }).flatten).setType(tpe)

    case _ =>
      super[SMTLIBTarget].fromSMT(s, tpe)
  }

  override def toSMT(e: Expr)(implicit bindings: Map[Identifier, SExpr]) = e match {
    case a @ FiniteArray(elems) =>
      val tpe @ ArrayType(base) = normalizeType(a.getType)
      declareSort(tpe)

      var ar: SExpr = declareVariable(FreshIdentifier("arrayconst").setType(RawArrayType(Int32Type, base)))

      for ((e, i) <- elems.zipWithIndex) {
        ar = SList(SSymbol("store"), ar, toSMT(IntLiteral(i)), toSMT(e))
      }

      SList(constructors.toB(tpe), toSMT(IntLiteral(elems.size)), ar)

    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems) =>
      if (elems.isEmpty) {
        SList(SSymbol("as"), SSymbol("emptyset"), declareSort(fs.getType))
      } else {
        SList(SSymbol("setenum") :: elems.map(toSMT).toList)
      }

    case SubsetOf(ss, s) =>
      SList(SSymbol("subseteq"), toSMT(ss), toSMT(s))

    case ElementOfSet(e, s) =>
      SList(SSymbol("in"), toSMT(e), toSMT(s))

    case SetDifference(a, b) =>
      SList(SSymbol("setminus"), toSMT(a), toSMT(b))

    case SetUnion(a, b) =>
      SList(SSymbol("union"), toSMT(a), toSMT(b))

    case SetIntersection(a, b) =>
      SList(SSymbol("intersection"), toSMT(a), toSMT(b))

    case _ =>
      super[SMTLIBTarget].toSMT(e)
  }
}
