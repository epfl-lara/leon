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
import _root_.smtlib.interpreters.Z3Interpreter

import _root_.smtlib.Commands.NonStandardCommand

trait SMTLIBZ3Target extends SMTLIBTarget {
  this: SMTLIBSolver =>

  def targetName = "z3"

  def getNewInterpreter() = new Z3Interpreter

  val extSym = SSymbol("_")

  var setSort: Option[SSymbol] = None

  override def declareSort(t: TypeTree): SExpr = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case SetType(base) =>
          declareSetSort(base)
        case _ => super.declareSort(t)
      }
    }
  }

  def declareSetSort(of: TypeTree) = {
    setSort match {
      case None =>
        val s = SSymbol("Set")
        val t = SSymbol("T")
        setSort = Some(s)

        val cmd = NonStandardCommand(SList(SSymbol("define-sort"), s, SList(t), SList(SSymbol("Array"), t, SSymbol("Bool"))))
        sendCommand(cmd)
      case _ =>
    }

    SList(setSort.get, declareSort(of))
  }


  override def toSMT(e: Expr)(implicit bindings: Map[Identifier, SExpr]) = e match {
      case fs @ FiniteSet(elems) =>
        val ss = declareSort(fs.getType)
        var res = SList(SList(SSymbol("as"), SSymbol("const"), ss), toSMT(BooleanLiteral(false)))

        for (e <- elems) {
          res = SList(SSymbol("store"), res, toSMT(e), toSMT(BooleanLiteral(true)))
        }

        res

      case sd @ SetDifference(a, b) =>
        // a -- b
        // becomes:
        // a && not(b)
        SList(SList(extSym, SSymbol("map"), SSymbol("and")), toSMT(a), SList(SList(extSym, SSymbol("map"), SSymbol("not")), toSMT(b)))
      case SetUnion(l, r) =>
        SList(SList(extSym, SSymbol("map"), SSymbol("or")), toSMT(l), toSMT(r))

      case SetIntersection(l, r) =>
        SList(SList(extSym, SSymbol("map"), SSymbol("and")), toSMT(l), toSMT(r))

      case _ =>
        super.toSMT(e)
  }
}
