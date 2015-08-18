/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Expressions._
import purescala.Constructors._

case object BaseGrammar extends ExpressionGrammar[TypeTree] {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Gen] = t match {
    case BooleanType =>
      List(
        terminal(BooleanLiteral(true)),
        terminal(BooleanLiteral(false)),
        nonTerminal(List(BooleanType),              { case Seq(a)    => not(a) }),
        nonTerminal(List(BooleanType, BooleanType), { case Seq(a, b) => and(a, b) }),
        nonTerminal(List(BooleanType, BooleanType), { case Seq(a, b) => or(a, b) }),
        nonTerminal(List(Int32Type,   Int32Type),   { case Seq(a, b) => LessThan(a, b) }),
        nonTerminal(List(Int32Type,   Int32Type),   { case Seq(a, b) => LessEquals(a, b) }),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a, b) => LessThan(a, b) }),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a, b) => LessEquals(a, b) })
      )
    case Int32Type =>
      List(
        terminal(IntLiteral(0)),
        terminal(IntLiteral(1)),
        nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => plus(a, b) }),
        nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => minus(a, b) }),
        nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => times(a, b) })
      )

    case IntegerType =>
      List(
        terminal(InfiniteIntegerLiteral(0)),
        terminal(InfiniteIntegerLiteral(1)),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => plus(a, b) }),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => minus(a, b) }),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => times(a, b) })
      )

    case TupleType(stps) =>
      List(
        nonTerminal(stps, { sub => Tuple(sub) })
      )

    case cct: CaseClassType =>
      List(
        nonTerminal(cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
      )

    case act: AbstractClassType =>
      act.knownCCDescendants.map { cct =>
        nonTerminal(cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
      }

    case st @ SetType(base) =>
      List(
        nonTerminal(List(base),   { case elems     => FiniteSet(elems.toSet, base) }),
        nonTerminal(List(st, st), { case Seq(a, b) => SetUnion(a, b) }),
        nonTerminal(List(st, st), { case Seq(a, b) => SetIntersection(a, b) }),
        nonTerminal(List(st, st), { case Seq(a, b) => SetDifference(a, b) })
      )

    case UnitType =>
      List(
        terminal(UnitLiteral())
      )

    case _ =>
      Nil
  }
}
