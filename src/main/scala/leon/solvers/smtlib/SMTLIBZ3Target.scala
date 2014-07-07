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
import TreeOps.simplestValue

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.Commands.{DefineSort, GetValue, NonStandardCommand, GetModel, DefineFun}
import _root_.smtlib.interpreters.Z3Interpreter
import _root_.smtlib.parser.CommandsResponses.{SExprResponse, GetModelResponse}
import _root_.smtlib.theories.Core._
import _root_.smtlib.theories.ArraysEx

trait SMTLIBZ3Target extends SMTLIBTarget {
  this: SMTLIBSolver =>

  def targetName = "z3"

  def getNewInterpreter() = new Z3Interpreter

  val extSym = SSymbol("_")

  var setSort: Option[SSymbol] = None
  var mapSort: Option[SSymbol] = None
  var optionSort: Option[SSymbol] = None

  override def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case MapType(from, to) =>
          declareMapSort(from, to)
        case SetType(base) =>
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

  def declareOptionSort(of: TypeTree): Sort = {
    optionSort match {
      case None =>
        val t      = SSymbol("T")

        val s      = SSymbol("Option")
        val some   = SSymbol("Some")
        val some_v = SSymbol("Some_v")
        val none   = SSymbol("None")

        val caseSome = SList(some, SList(some_v, t))
        val caseNone = none

        val cmd = NonStandardCommand(SList(SSymbol("declare-datatypes"), SList(t), SList(SList(s, caseSome, caseNone))))
        sendCommand(cmd)

        optionSort = Some(s)
      case _ =>
    }

    Sort(SMTIdentifier(optionSort.get), Seq(declareSort(of)))
  }

  def declareMapSort(from: TypeTree, to: TypeTree): Sort = {
    mapSort match {
      case None =>
        val m = SSymbol("Map")
        val a = SSymbol("A")
        val b = SSymbol("B")
        mapSort = Some(m)
        declareOptionSort(to)

        val arraySort = Sort(SMTIdentifier(SSymbol("Array")),
                             Seq(Sort(SMTIdentifier(optionSort.get)), Sort(SMTIdentifier(b))))

        val cmd = DefineSort(m, Seq(a, b), arraySort)
        sendCommand(cmd)
      case _ =>
    }

    Sort(SMTIdentifier(mapSort.get), Seq(declareSort(from), declareSort(to)))
  }

  override def fromSMT(s: Term, tpe: TypeTree)(implicit letDefs: Map[SSymbol, Term]): Expr = (s, tpe) match {
    case (SimpleSymbol(s), tp: TypeParameter) =>
      val n = s.name.split("!").toList.last
      GenericValue(tp, n.toInt)


    //case (SList(List(`extSym`, SSymbol("as-array"), k: SSymbol)), tpe) =>
    //  if (letDefs contains k) {
    //    // Need to recover value form function model
    //    fromRawArray(extractRawArray(letDefs(k)), tpe)
    //  } else {
    //    unsupported(" as-array on non-function or unknown symbol "+k)
    //  }

    // SMT representation for empty sets: Array(* -> false)
    //case (SList(List(SList(List(SSymbol("as"), SSymbol("const"), SList(List(SSymbol("Array"), k, v)))), defV)), tpe) =>
    //  val ktpe = sorts.fromB(Sort(SMTIdentifier(k)))
    //  val vtpe = sorts.fromB(Sort(SMTIdentifier(v)))

    //  fromRawArray(RawArrayValue(ktpe, Map(), fromSMT(defV, vtpe)), tpe)

    case _ =>
      super[SMTLIBTarget].fromSMT(s, tpe)
  }

  override def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {
      //case a @ FiniteArray(elems) =>
      //  val tpe @ ArrayType(base) = normalizeType(a.getType)
      //  declareSort(tpe)

      //  var ar = SList(SList(SSymbol("as"), SSymbol("const"), declareSort(RawArrayType(Int32Type, base))), toSMT(simplestValue(base)))

      //  for ((e, i) <- elems.zipWithIndex) {
      //    ar = SList(SSymbol("store"), ar, toSMT(IntLiteral(i)), toSMT(e))
      //  }

      //  SList(constructors.toB(tpe), toSMT(IntLiteral(elems.size)), ar)

      ///**
      // * ===== Map operations =====
      // */
      //case MapGet(m, k) =>
      //  declareSort(m.getType)
      //  SList(SSymbol("Some_v"), SList(SSymbol("select"), toSMT(m), toSMT(k)))

      //case MapIsDefinedAt(m, k) =>
      //  declareSort(m.getType)
      //  SList(SSymbol("is-Some"), SList(SSymbol("select"), toSMT(m), toSMT(k)))

      //case m @ FiniteMap(elems) =>
      //  val ms = declareSort(m.getType)

      //  var res = SList(SList(SSymbol("as"), SSymbol("const"), ms), SSymbol("None"))
      //  for ((k, v) <- elems) {
      //    res = SList(SSymbol("store"), res, toSMT(k), SList(SSymbol("Some"), toSMT(v)))
      //  }

      //  res

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

      //case SubsetOf(ss, s) =>
      //  // a isSubset b   ==>   (a zip b).map(implies) == (* => true)
      //  val allTrue    = SList(SList(SSymbol("as"), SSymbol("const"), declareSort(s.getType)), SSymbol("true"))
      //  val mapImplies = SList(SList(extSym, SSymbol("map"), SSymbol("implies")), toSMT(ss), toSMT(s))

      //  SList(SSymbol("="), mapImplies, allTrue)

      //case ElementOfSet(e, s) =>
      //  SList(SSymbol("select"), toSMT(s), toSMT(e))

      //case SetDifference(a, b) =>
      //  // a -- b
      //  // becomes:
      //  // a && not(b)
      //  SList(SList(extSym, SSymbol("map"), SSymbol("and")), toSMT(a), SList(SList(extSym, SSymbol("map"), SSymbol("not")), toSMT(b)))
      case SetUnion(l, r) =>
        FunctionApplication(
          QualifiedIdentifier(SMTIdentifier(SSymbol("(_ map or)"))), //hack to get around Z3 syntax
          Seq(toSMT(l), toSMT(r)))

      //case SetIntersection(l, r) =>
      //  SList(SList(extSym, SSymbol("map"), SSymbol("and")), toSMT(l), toSMT(r))

      case _ =>
        super.toSMT(e)
  }

  def extractRawArray(s: SExpr)(implicit letDefs: Map[SSymbol, SExpr]): RawArrayValue = s match {
    //case SList(List(SSymbol("define-fun"), a: SSymbol, SList(SList(List(arg, akind)) :: Nil), rkind, body)) =>
    //  val argTpe = sorts.toA(Sort(SMTIdentifier(akind)))
    //  val retTpe = sorts.toA(Sort(SMTIdentifier(rkind)))

    //  def extractCases(e: SExpr): (Map[Expr, Expr], Expr) = e match {
    //    case SList(SSymbol("ite") :: SList(SSymbol("=") :: `arg` :: k :: Nil) :: v :: e :: Nil) =>
    //      val (cs, d) = extractCases(e)
    //      (Map(fromSMT(k, argTpe) -> fromSMT(v, retTpe)) ++ cs, d)
    //    case e =>
    //      (Map(),fromSMT(e, retTpe))
    //  }

    //  val (cases, default) = extractCases(body)

    //  RawArrayValue(argTpe, cases, default)
    case _ =>
      unsupported("Unable to extract "+s)
  }

  def fromRawArray(r: RawArrayValue, tpe: TypeTree): Expr = tpe match {
    case SetType(base) =>
      assert(r.default == BooleanLiteral(false) && r.keyTpe == base)

      FiniteSet(r.elems.keySet.toSeq).setType(tpe)

    case RawArrayType(from, to) =>
      r

    case _ =>
      unsupported("Unable to extract from raw array for "+tpe)
  }

  // EK: We use get-model instead in order to extract models for arrays
  override def getModel: Map[Identifier, Expr] = {

    val cmd = GetModel()

    val res = sendCommand(cmd)

    val smodel: Seq[DefineFun] = res match {
      case GetModelResponse(model) => model
      case _ => Nil
    }

    var modelFunDefs = Map[SSymbol, DefineFun]()

    // First pass to gather functions (arrays defs)
    for (me <- smodel) me match {
      case DefineFun(a, args, _, _) if args.nonEmpty =>
        modelFunDefs += a -> me
      case _ =>
    }

    var model = Map[Identifier, Expr]()

    for (me <- smodel) me match {
      case DefineFun(s, args, kind, e) =>
        if(args.isEmpty) {
          val id = variables.toA(s)
          // EK: this is a little hack, we pass models for array functions as let-defs
          model += id -> fromSMT(e, id.getType)(null)//modelFunDefs)
        }
    }


    model
  }
}
