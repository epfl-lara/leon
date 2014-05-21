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

trait SMTLIBCVC4Target extends SMTLIBTarget {
  this: SMTLIBSolver =>

  val targetName = "cvc4"

  def getNewInterpreter() = new CVC4Interpreter

  val extSym = SSymbol("_")

  override def toSMT(e: Expr)(implicit bindings: Map[Identifier, SExpr]) = e match {
      case fs @ FiniteSet(elems) =>
        val ss = declareSort(fs.getType)
        var res = SList(SSymbol("as"), SSymbol("const"), ss, toSMT(BooleanLiteral(false)))

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
