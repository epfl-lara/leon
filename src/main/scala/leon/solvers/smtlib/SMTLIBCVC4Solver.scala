/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import OptionParsers._

import purescala._
import Definitions.Program
import Common._
import Expressions.{Assert => _, _}
import Extractors._
import Constructors._
import Types._

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, ForAll => SMTForall, _}
import _root_.smtlib.parser.Commands._
import _root_.smtlib.interpreters.CVC4Interpreter
import _root_.smtlib.theories._

class SMTLIBCVC4Solver(context: LeonContext, program: Program) extends SMTLIBSolver(context, program) {

  def targetName = "cvc4"

  def userDefinedOps(ctx: LeonContext) = {
    ctx.findOptionOrDefault(SMTLIBCVC4Component.optCVC4Options)
  }

  def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--produce-models",
      "--incremental",
//      "--no-incremental",
//      "--tear-down-incremental",
//      "--dt-rewrite-error-sel", // Removing since it causes CVC4 to segfault on some inputs
      "--rewrite-divk",
      "--print-success",
      "--lang", "smt"
    ) ++ userDefinedOps(ctx).toSeq
  }

  def getNewInterpreter(ctx: LeonContext) = {
    val opts = interpreterOps(ctx)
    reporter.debug("Invoking solver with "+opts.mkString(" "))
    new CVC4Interpreter("cvc4", opts.toArray)
  }

  override def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case TypeParameter(id) =>
          val s = id2sym(id)
          val cmd = DeclareSort(s, 0)
          sendCommand(cmd)
          Sort(SMTIdentifier(s))

        case SetType(base) =>
          Sort(SMTIdentifier(SSymbol("Set")), Seq(declareSort(base)))

        case _ =>
          super.declareSort(t)
      }
    }
  }

  override def fromSMT(s: Term, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = (s, tpe) match {
    case (SimpleSymbol(s), tp: TypeParameter) =>
      val n = s.name.split("_").toList.last
      GenericValue(tp, n.toInt)

    case (QualifiedIdentifier(SMTIdentifier(SSymbol("emptyset"), Seq()), _), SetType(base)) =>
      EmptySet(base)

    case (FunctionApplication(SimpleSymbol(SSymbol("__array_store_all__")), Seq(_, elem)), RawArrayType(k,v)) =>
      RawArrayValue(k, Map(), fromSMT(elem, v))

    case (FunctionApplication(SimpleSymbol(SSymbol("store")), Seq(arr, key, elem)), RawArrayType(k,v)) =>
      val RawArrayValue(_, elems, base) = fromSMT(arr, tpe)
      RawArrayValue(k, elems + (fromSMT(key, k) -> fromSMT(elem, v)), base)

    case (FunctionApplication(SimpleSymbol(SSymbol("singleton")), elems), SetType(base)) =>
      finiteSet(elems.map(fromSMT(_, base)).toSet, base)

    case (FunctionApplication(SimpleSymbol(SSymbol("insert")), elems), SetType(base)) =>
      val selems = elems.init.map(fromSMT(_, base))
      val FiniteSet(se) = fromSMT(elems.last, tpe)
      finiteSet(se ++ selems, base)

    case (FunctionApplication(SimpleSymbol(SSymbol("union")), elems), SetType(base)) =>
      finiteSet(elems.map(fromSMT(_, tpe) match {
        case FiniteSet(elems) => elems
      }).flatten.toSet, base)

    // FIXME (nicolas)
    // some versions of CVC4 seem to generate array constants with "as const" notation instead of the __array_store_all__
    // one I've witnessed up to now. Don't know why this is happening...
    case (FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), _), Seq(elem)), ft @ FunctionType(from, to)) =>
      finiteLambda(fromSMT(elem, to), Seq.empty, from)

    case (FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), _), Seq(elem)), RawArrayType(k, v)) =>
      RawArrayValue(k, Map(), fromSMT(elem, v))

    case _ =>
      super.fromSMT(s, tpe)
  }

  override def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]) = e match {
    case a @ FiniteArray(elems, default, size) =>
      val tpe @ ArrayType(base) = normalizeType(a.getType)
      declareSort(tpe)

      var ar: Term = declareVariable(FreshIdentifier("arrayconst", RawArrayType(Int32Type, base)))

      for ((i, e) <- elems) {
        ar = FunctionApplication(SSymbol("store"), Seq(ar, toSMT(IntLiteral(i)), toSMT(e)))
      }

      FunctionApplication(constructors.toB(tpe), Seq(toSMT(size), ar))

    case fm @ FiniteMap(elems) =>
      import OptionManager._
      val mt @ MapType(from, to) = fm.getType
      declareSort(mt)

      var m: Term = declareVariable(FreshIdentifier("mapconst", RawArrayType(from, leonOptionType(to))))

      sendCommand(Assert(SMTForall(
        SortedVar(SSymbol("mapelem"), declareSort(from)), Seq(),
        Core.Equals(
          ArraysEx.Select(m, SSymbol("mapelem")),
          toSMT(mkLeonNone(to))
        )
      )))

      for ((k, v) <- elems) {
        m = FunctionApplication(SSymbol("store"), Seq(m, toSMT(k), toSMT(mkLeonSome(v))))
      }

      m

    /**
     * ===== Set operations =====
     */


    case fs @ FiniteSet(elems) =>
      if (elems.isEmpty) {
        QualifiedIdentifier(SMTIdentifier(SSymbol("emptyset")), Some(declareSort(fs.getType)))
      } else {
        val selems = elems.toSeq.map(toSMT)

        val sgt = FunctionApplication(SSymbol("singleton"), Seq(selems.head))

        if (selems.size > 1) {
          FunctionApplication(SSymbol("insert"), selems.tail :+ sgt)
        } else {
          sgt
        }
      }

    case SubsetOf(ss, s) =>
      FunctionApplication(SSymbol("subset"), Seq(toSMT(ss), toSMT(s)))

    case ElementOfSet(e, s) =>
      FunctionApplication(SSymbol("member"), Seq(toSMT(e), toSMT(s)))

    case SetDifference(a, b) =>
      FunctionApplication(SSymbol("setminus"), Seq(toSMT(a), toSMT(b)))

    case SetUnion(a, b) =>
      FunctionApplication(SSymbol("union"), Seq(toSMT(a), toSMT(b)))

    case SetIntersection(a, b) =>
      FunctionApplication(SSymbol("intersection"), Seq(toSMT(a), toSMT(b)))

    case _ =>
      super.toSMT(e)
  }
}

object SMTLIBCVC4Component extends LeonComponent {
  val name = "cvc4 solver"

  val description = "Solver invoked when --solvers=smt-cvc4"

  val optCVC4Options = new LeonOptionDef[Set[String]] {
    val name = "solver:cvc4"
    val description = "Pass extra arguments to CVC4"
    val default = Set[String]()
    val parser = setParser(stringParser)
    val usageRhs = "<cvc4-opt>"
  }

  override val definedOptions : Set[LeonOptionDef[Any]] = Set(optCVC4Options)
}
