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
import _root_.smtlib.Commands.{GetValue, NonStandardCommand}
import _root_.smtlib.CommandResponses.SExprResponse

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

  override def extractSpecialSymbols(s: SSymbol): Option[Expr] = {
    s.s.split("!").toList.reverse match {
      case n :: "val" :: rest =>
        val sort = rest.reverse.mkString("!")

        sorts.getA(SSymbol(sort)) match {
          case Some(tp : TypeParameter) =>
            Some(GenericValue(tp, n.toInt))
          case _ =>
            None
        }
      case _ =>
        None
    }
  }

  override def fromSMT(s: SExpr)(implicit bindings: Map[SSymbol, Expr]): Expr = s match {
    case SList(List(`extSym`, SSymbol("as-array"), k: SSymbol)) =>
      bindings(k)

    // SMT representation for empty sets: Array(* -> false)
    case SList(List(SList(List(SSymbol("as"), SSymbol("const"), SList(List(SSymbol("Array"), s, SSymbol("Bool"))))), SSymbol("false"))) =>
      FiniteSet(Nil).setType(sorts.fromB(s))

    case _ =>
      super.fromSMT(s)
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

  // We use get-model instead
  override def getModel: Map[Identifier, Expr] = {

    val cmd = NonStandardCommand(SList(SSymbol("get-model")))

    val res = sendCommand(cmd)

    val smodel = res match {
      case SExprResponse(SList(SSymbol("model") :: entries)) => entries
      case _ => Nil
    }

    var maps = Map[SSymbol, TypeTree]()

    // First pass to gather functions (arrays defs)
    for (me <- smodel) me match {
      case SList(List(SSymbol("define-fun"), a: SSymbol, SList(Nil), _, SList(List(`extSym`, SSymbol("as-array"), k: SSymbol)))) =>
        maps += k -> variables.toA(a).getType
      case _ =>
    }

    var bindings = Map[SSymbol, Expr]()

    // Second pass to gather functions (arrays defs)
    for (me <- smodel) me match {
      case SList(List(SSymbol("define-fun"), s: SSymbol, SList(SList(List(arg, _)) :: Nil), _, e)) if maps contains s =>
        def extractCases(e: SExpr): (Map[Expr, Expr], Expr) = e match {
          case SList(SSymbol("ite") :: SList(SSymbol("=") :: `arg` :: k :: Nil) :: v :: e :: Nil) =>
            val (cs, d) = extractCases(e)
            (Map(fromSMT(k)(Map()) -> fromSMT(v)(Map())) ++ cs, d)
          case e =>
            (Map(),fromSMT(e)(Map()))
        }

        def buildValue(cases: Map[Expr, Expr], default: Expr, tpe: TypeTree): Expr = tpe match {
          case SetType(base) =>
            assert(default == BooleanLiteral(false))
            FiniteSet(cases.keySet.toSeq).setType(tpe)
          case _ =>
            unsupported("Cannot build array/map model to "+tpe)
        }

        val tpe = maps(s)
        val (cases, default) = extractCases(e)

        bindings += s -> buildValue(cases, default, tpe)
      case _ =>
    }

    var model = Map[Identifier, Expr]()

    for (me <- smodel) me match {
      case SList(List(SSymbol("define-fun"), s: SSymbol, SList(args), kind, e)) =>
        if (args.isEmpty) {
          model += variables.toA(s) -> fromSMT(e)(bindings)
        }

      case SList(SSymbol("forall") :: _) => // no body
        // Ignore

      case SList(SSymbol("declare-fun") :: _) => // no body
        // Ignore

      case _ =>
        unsupported("Unknown model entry: "+me)
    }


    model
  }
}
