/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala._
import Common._
import Expressions.{Assert => _, _}
import Extractors._
import Constructors._
import Types._

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, Forall => SMTForall, _}
import _root_.smtlib.parser.Commands._

trait SMTLIBCVC4Target extends SMTLIBTarget {
  override def declareSort(t: TypeTree): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case TypeParameter(id) =>
          val s = id2sym(id)
          val cmd = DeclareSort(s, 0)
          emit(cmd)
          Sort(SMTIdentifier(s))

        case SetType(base) =>
          Sort(SMTIdentifier(SSymbol("Set")), Seq(declareSort(base)))

        case _ =>
          super.declareSort(t)
      }
    }
  }

  override def fromSMT(s: Term, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = (s, tpe) match {
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

    case (FunctionApplication(SimpleSymbol(SSymbol("__array_store_all__")), Seq(_, elem)), ft @ FunctionType(from,to)) =>
      finiteLambda(fromSMT(elem, to), Seq.empty, from)

    case (FunctionApplication(SimpleSymbol(SSymbol("store")), Seq(arr, key, elem)), RawArrayType(k,v)) =>
      val RawArrayValue(_, elems, base) = fromSMT(arr, tpe)
      RawArrayValue(k, elems + (fromSMT(key, k) -> fromSMT(elem, v)), base)

    case (FunctionApplication(SimpleSymbol(SSymbol("store")), Seq(arr, key, elem)), ft @ FunctionType(from,to)) =>
      val FiniteLambda(dflt, mapping) = fromSMT(arr, tpe)
      finiteLambda(dflt, mapping :+ (fromSMT(key, tupleTypeWrap(from)) -> fromSMT(elem, to)), from)

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
