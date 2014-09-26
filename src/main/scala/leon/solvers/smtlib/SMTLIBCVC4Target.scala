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

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.Commands._
import _root_.smtlib.interpreters.CVC4Interpreter

trait SMTLIBCVC4Target extends SMTLIBTarget {
  this: SMTLIBSolver =>

  def targetName = "cvc4"

  def getNewInterpreter() = new CVC4Interpreter

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
          super[SMTLIBTarget].declareSort(t)
      }
    }
  }

  override def fromSMT(s: Term, tpe: TypeTree)(implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = (s, tpe) match {
    case (SimpleSymbol(s), tp: TypeParameter) =>
      val n = s.name.split("_").toList.last
      GenericValue(tp, n.toInt)

    case (QualifiedIdentifier(SMTIdentifier(SSymbol("emptyset"), Seq()), _), SetType(base)) =>
      FiniteSet(Set()).setType(tpe)

    case (FunctionApplication(SimpleSymbol(SSymbol("setenum")), elems), SetType(base)) =>
      FiniteSet(elems.map(fromSMT(_, base)).toSet).setType(tpe)

    case (FunctionApplication(SimpleSymbol(SSymbol("union")), elems), SetType(base)) =>
      FiniteSet(elems.map(fromSMT(_, tpe) match {
        case FiniteSet(elems) => elems
      }).flatten.toSet).setType(tpe)

    case _ =>
      super[SMTLIBTarget].fromSMT(s, tpe)
  }

  override def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]) = e match {
    case a @ FiniteArray(elems) =>
      val tpe @ ArrayType(base) = normalizeType(a.getType)
      declareSort(tpe)

      var ar: Term = declareVariable(FreshIdentifier("arrayconst").setType(RawArrayType(Int32Type, base)))

      for ((e, i) <- elems.zipWithIndex) {
        ar = FunctionApplication(SSymbol("store"), Seq(ar, toSMT(IntLiteral(i)), toSMT(e)))
      }

      FunctionApplication(constructors.toB(tpe), Seq(toSMT(IntLiteral(elems.size)), ar))

    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems) =>
      if (elems.isEmpty) {
        QualifiedIdentifier(SMTIdentifier(SSymbol("emptyset")), Some(declareSort(fs.getType)))
      } else {
        FunctionApplication(SSymbol("singleton"), elems.toSeq.map(toSMT))
      }

    case SubsetOf(ss, s) =>
      FunctionApplication(SSymbol("subseteq"), Seq(toSMT(ss), toSMT(s)))

    case ElementOfSet(e, s) =>
      FunctionApplication(SSymbol("in"), Seq(toSMT(e), toSMT(s)))

    case SetDifference(a, b) =>
      FunctionApplication(SSymbol("setminus"), Seq(toSMT(a), toSMT(b)))

    case SetUnion(a, b) =>
      FunctionApplication(SSymbol("union"), Seq(toSMT(a), toSMT(b)))

    case SetIntersection(a, b) =>
      FunctionApplication(SSymbol("intersection"), Seq(toSMT(a), toSMT(b)))

    case _ =>
      super[SMTLIBTarget].toSMT(e)
  }
}
