/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, Forall => SMTForall, _}
import _root_.smtlib.parser.Commands._
import _root_.smtlib.interpreters.CVC4Interpreter

trait SMTLIBCVC4Target extends SMTLIBTarget {

  override def getNewInterpreter(ctx: LeonContext) = {
    val opts = interpreterOps(ctx)
    reporter.debug("Invoking solver with "+opts.mkString(" "))

    new CVC4Interpreter("cvc4", opts.toArray)
  }

  override protected def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case SetType(base) =>
          Sort(SMTIdentifier(SSymbol("Set")), Seq(declareSort(base)))

        case _ =>
          super.declareSort(t)
      }
    }
  }

  override protected def fromSMT(s: Term, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = (s, tpe) match {
    // EK: This hack is necessary for sygus which does not strictly follow smt-lib for negative literals
    case (SimpleSymbol(SSymbol(v)), IntegerType) if v.startsWith("-") =>
      try {
        InfiniteIntegerLiteral(v.toInt)
      } catch {
        case t: Throwable =>
          super.fromSMT(s, tpe)
      }

    case (SimpleSymbol(s), tp: TypeParameter) =>
      val n = s.name.split("_").toList.last
      GenericValue(tp, n.toInt)

    case (QualifiedIdentifier(SMTIdentifier(SSymbol("emptyset"), Seq()), _), SetType(base)) =>
      FiniteSet(Set(), base)

    case (FunctionApplication(SimpleSymbol(SSymbol("__array_store_all__")), Seq(_, elem)), RawArrayType(k,v)) =>
      RawArrayValue(k, Map(), fromSMT(elem, v))

    case (FunctionApplication(SimpleSymbol(SSymbol("__array_store_all__")), Seq(_, elem)), FunctionType(from,to)) =>
      RawArrayValue(tupleTypeWrap(from), Map(), fromSMT(elem, to))

    case (FunctionApplication(SimpleSymbol(SSymbol("store")), Seq(arr, key, elem)), RawArrayType(k,v)) =>
      val RawArrayValue(_, elems, base) = fromSMT(arr, tpe)
      RawArrayValue(k, elems + (fromSMT(key, k) -> fromSMT(elem, v)), base)

    case (FunctionApplication(SimpleSymbol(SSymbol("store")), Seq(arr, key, elem)), FunctionType(from,to)) =>
      val RawArrayValue(k, elems, base) = fromSMT(arr, tpe)
      RawArrayValue(k, elems + (fromSMT(key, k) -> fromSMT(elem, to)), base)

    case (FunctionApplication(SimpleSymbol(SSymbol("singleton")), elems), SetType(base)) =>
      FiniteSet(elems.map(fromSMT(_, base)).toSet, base)

    case (FunctionApplication(SimpleSymbol(SSymbol("insert")), elems), SetType(base)) =>
      val selems = elems.init.map(fromSMT(_, base))
      val FiniteSet(se, _) = fromSMT(elems.last, tpe)
      FiniteSet(se ++ selems, base)

    case (FunctionApplication(SimpleSymbol(SSymbol("union")), elems), SetType(base)) =>
      FiniteSet(elems.flatMap(fromSMT(_, tpe) match {
        case FiniteSet(elems, _) => elems
      }).toSet, base)

    case (FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), _), Seq(elem)), RawArrayType(k, v)) =>
      RawArrayValue(k, Map(), fromSMT(elem, v))

    // FIXME (nicolas)
    // some versions of CVC4 seem to generate array constants with "as const" notation instead of the __array_store_all__
    // one I've witnessed up to now. Don't know why this is happening...
    case (FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), _), Seq(elem)), FunctionType(from, to)) =>
      RawArrayValue(tupleTypeWrap(from), Map(), fromSMT(elem, to))

    case _ =>
      super.fromSMT(s, tpe)
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]) = e match {
    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems, _) =>
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
