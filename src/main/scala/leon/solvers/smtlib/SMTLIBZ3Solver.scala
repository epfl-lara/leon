/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala._
import Common._
import Definitions.Program
import Expressions._
import Extractors._
import Types._
import Constructors._
import ExprOps.simplestValue

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.interpreters.Z3Interpreter
import _root_.smtlib.parser.CommandsResponses.GetModelResponseSuccess
import _root_.smtlib.theories.Core.{Equals => SMTEquals, _}
import _root_.smtlib.theories.ArraysEx

class SMTLIBZ3Solver(context: LeonContext, program: Program) extends SMTLIBSolver(context, program) {

  def targetName = "z3"

  def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-in",
      "-smt2"
    )
  }

  def getNewInterpreter(ctx: LeonContext) = new Z3Interpreter("z3", interpreterOps(ctx).toArray)

  val extSym = SSymbol("_")

  var setSort: Option[SSymbol] = None

  override def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case SetType(base) =>
          super.declareSort(BooleanType)
          declareSetSort(base)
        case _ =>
          super.declareSort(t)
      }
    }
  }

  def declareSetSort(of: TypeTree): Sort = {
    setSort match {
      case None =>
        val s = SSymbol("Set")
        val t = SSymbol("T")
        setSort = Some(s)

        val arraySort = Sort(SMTIdentifier(SSymbol("Array")), 
                             Seq(Sort(SMTIdentifier(t)), BoolSort()))

        val cmd = DefineSort(s, Seq(t), arraySort)
        sendCommand(cmd)
      case _ =>
    }

    Sort(SMTIdentifier(setSort.get), Seq(declareSort(of)))
  }

  override def fromSMT(s: Term, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = (s, tpe) match {
    case (SimpleSymbol(s), tp: TypeParameter) =>
      val n = s.name.split("!").toList.last
      GenericValue(tp, n.toInt)

    // XXX: (NV) Z3 doesn't seem to produce models for uninterpreted functions that
    //      don't impact satisfiability...
    case (SNumeral(n), ft: FunctionType) if !letDefs.isDefinedAt(lambdas.toB(ft)) =>
      simplestValue(ft)

    case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), tpe) =>
      if (letDefs contains k) {
        // Need to recover value form function model
        fromRawArray(extractRawArray(letDefs(k), tpe), tpe)
      } else {
        unsupported(" as-array on non-function or unknown symbol "+k)
      }

    case (FunctionApplication(
      QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), Some(ArraysEx.ArraySort(k, v))),
      Seq(defV)
    ), tpe) =>
      val ktpe = sorts.fromB(k)
      val vtpe = sorts.fromB(v)

      fromRawArray(RawArrayValue(ktpe, Map(), fromSMT(defV, vtpe)), tpe)

    case _ =>
      super.fromSMT(s, tpe)
  }

  override def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {
    case a @ FiniteArray(elems, oDef, size) =>
      val tpe @ ArrayType(base) = normalizeType(a.getType)
      declareSort(tpe)

      val default: Expr = oDef.getOrElse(simplestValue(base))

      var ar: Term = ArrayConst(declareSort(RawArrayType(Int32Type, base)), toSMT(default))

      for ((i, e) <- elems) {
        ar = ArraysEx.Store(ar, toSMT(IntLiteral(i)), toSMT(e))
      }

      FunctionApplication(constructors.toB(tpe), List(toSMT(size), ar))

    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems) =>
      val ss = declareSort(fs.getType)
      var res: Term = FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const")), Some(ss)),
        Seq(toSMT(BooleanLiteral(false)))
      )

      for (e <- elems) {
        res = ArraysEx.Store(res, toSMT(e), toSMT(BooleanLiteral(true)))
      }

      res

    case SubsetOf(ss, s) =>
      // a isSubset b   ==>   (a zip b).map(implies) == (* => true)
      val allTrue = ArrayConst(declareSort(s.getType), True())

      SMTEquals(ArrayMap(SSymbol("implies"), toSMT(ss), toSMT(s)), allTrue)

    case ElementOfSet(e, s) =>
      ArraysEx.Select(toSMT(s), toSMT(e))

    case SetDifference(a, b) =>
      // a -- b
      // becomes:
      // a && not(b)

      ArrayMap(SSymbol("and"), toSMT(a), ArrayMap(SSymbol("not"), toSMT(b)))

    case SetUnion(l, r) =>
      ArrayMap(SSymbol("or"), toSMT(l), toSMT(r))

    case SetIntersection(l, r) =>
      ArrayMap(SSymbol("and"), toSMT(l), toSMT(r))

    case _ =>
      super.toSMT(e)
  }

  def extractRawArray(s: DefineFun, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): RawArrayValue = s match {
    case DefineFun(SMTFunDef(a, Seq(SortedVar(arg, akind)), rkind, body)) =>
      val (argTpe, retTpe) = tpe match {
        case SetType(base) => (base, BooleanType)
        case ArrayType(base) => (Int32Type, base)
        case RawArrayType(from, to) => (from, to)
        case _ => unsupported("Unsupported type for (un)packing into raw arrays: "+tpe +" (got kinds "+akind+" -> "+rkind+")")
      }

      def extractCases(e: Term): (Map[Expr, Expr], Expr) = e match {
        case ITE(SMTEquals(SimpleSymbol(`arg`), k), v, e) =>
          val (cs, d) = extractCases(e)
          (Map(fromSMT(k, argTpe) -> fromSMT(v, retTpe)) ++ cs, d)
        case e =>
          (Map(),fromSMT(e, retTpe))
      }

      val (cases, default) = extractCases(body)

      RawArrayValue(argTpe, cases, default)

    case _ =>
      unsupported("Unable to extract "+s)
  }

  object ArrayMap {
    def apply(op: SSymbol, arrs: Term*) = {
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("map"), List(op))),
        arrs
      )
    }
  }

  object ArrayConst {
    def apply(sort: Sort, default: Term) = {
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const")), Some(sort)),
        List(default))
    }
  }
}
