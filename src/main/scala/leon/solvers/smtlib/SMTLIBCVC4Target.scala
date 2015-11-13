/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Common._
import purescala.Expressions._
import purescala.Constructors._
import purescala.Types._

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, Forall => SMTForall, _}
import _root_.smtlib.parser.Commands._
import _root_.smtlib.interpreters.CVC4Interpreter
import _root_.smtlib.theories.experimental.Sets

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
          Sets.SetSort(declareSort(base))

        case _ =>
          super.declareSort(t)
      }
    }
  }

  override protected def fromSMT(t: Term, otpe: Option[TypeTree] = None)
                                (implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    (t, otpe) match {
      // EK: This hack is necessary for sygus which does not strictly follow smt-lib for negative literals
      case (SimpleSymbol(SSymbol(v)), Some(IntegerType)) if v.startsWith("-") =>
        try {
          InfiniteIntegerLiteral(v.toInt)
        } catch {
          case _: Throwable =>
            super.fromSMT(t, otpe)
        }

      case (SimpleSymbol(s), Some(tp: TypeParameter)) =>
        val n = s.name.split("_").toList.last
        GenericValue(tp, n.toInt)

      case (QualifiedIdentifier(SMTIdentifier(SSymbol("emptyset"), Seq()), _), Some(SetType(base))) =>
        FiniteSet(Set(), base)

      case (FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), _), Seq(elem)), Some(tpe)) =>
        tpe match {
          case RawArrayType(k, v) =>
            RawArrayValue(k, Map(), fromSMT(elem, v))

          case FunctionType(from, to) =>
            RawArrayValue(tupleTypeWrap(from), Map(), fromSMT(elem, to))

          case MapType(k, v) =>
            FiniteMap(Map(), k, v)

        }

      case (FunctionApplication(SimpleSymbol(SSymbol("__array_store_all__")), Seq(_, elem)), Some(tpe)) =>
        tpe match {
          case RawArrayType(k, v) =>
            RawArrayValue(k, Map(), fromSMT(elem, v))

          case FunctionType(from, to) =>
            RawArrayValue(tupleTypeWrap(from), Map(), fromSMT(elem, to))

          case MapType(k, v) =>
            FiniteMap(Map(), k, v)

        }

      case (FunctionApplication(SimpleSymbol(SSymbol("store")), Seq(arr, key, elem)), Some(tpe)) =>
        tpe match {
          case RawArrayType(_, v) =>
            val RawArrayValue(k, elems, base) = fromSMT(arr, otpe)
            RawArrayValue(k, elems + (fromSMT(key, k) -> fromSMT(elem, v)), base)

          case FunctionType(_, v) =>
            val RawArrayValue(k, elems, base) = fromSMT(arr, otpe)
            RawArrayValue(k, elems + (fromSMT(key, k) -> fromSMT(elem, v)), base)

          case MapType(k, v) =>
            val FiniteMap(elems, k, v) = fromSMT(arr, otpe)
            FiniteMap(elems + (fromSMT(key, k) -> fromSMT(elem, v)), k, v)
        }

      case (FunctionApplication(SimpleSymbol(SSymbol("singleton")), elems), Some(SetType(base))) =>
        FiniteSet(elems.map(fromSMT(_, base)).toSet, base)

      case (FunctionApplication(SimpleSymbol(SSymbol("insert")), elems), Some(SetType(base))) =>
        val selems = elems.init.map(fromSMT(_, base))
        val FiniteSet(se, _) = fromSMT(elems.last, otpe)
        FiniteSet(se ++ selems, base)

      case (FunctionApplication(SimpleSymbol(SSymbol("union")), elems), Some(SetType(base))) =>
        FiniteSet(elems.flatMap(fromSMT(_, otpe) match {
          case FiniteSet(elems, _) => elems
        }).toSet, base)

      case _ =>
        super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]) = e match {
    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems, _) =>
      if (elems.isEmpty) {
        Sets.EmptySet(declareSort(fs.getType))
      } else {
        val selems = elems.toSeq.map(toSMT)

        val sgt = Sets.Singleton(selems.head)

        if (selems.size > 1) {
          Sets.Insert(selems.tail :+ sgt)
        } else {
          sgt
        }
      }

    case SubsetOf(ss, s) => Sets.Subset(toSMT(ss), toSMT(s))
    case ElementOfSet(e, s) => Sets.Member(toSMT(e), toSMT(s))
    case SetDifference(a, b) => Sets.Setminus(toSMT(a), toSMT(b))
    case SetUnion(a, b) => Sets.Union(toSMT(a), toSMT(b))
    case SetIntersection(a, b) => Sets.Intersection(toSMT(a), toSMT(b))

    case _ =>
      super.toSMT(e)
  }
}
