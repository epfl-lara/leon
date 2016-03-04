/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Expressions._
import purescala.Constructors._

/** The basic grammar for Leon expressions.
  * Generates the most obvious expressions for a given type,
  * without regard of context (variables in scope, current function etc.)
  * Also does some trivial simplifications.
  */
case object BaseGrammar extends SimpleExpressionGrammar {

  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = t match {
    case BooleanType =>
      List(
        terminal(BooleanLiteral(false), Tags.BooleanC),
        terminal(BooleanLiteral(true),  Tags.BooleanC),
        nonTerminal(List(BooleanType), { case Seq(a) => not(a) }, Tags.Not),
        nonTerminal(List(BooleanType, BooleanType), { case Seq(a, b) => and(a, b) }, Tags.And),
        nonTerminal(List(BooleanType, BooleanType), { case Seq(a, b) => or(a, b)  }, Tags.Or ),
        nonTerminal(List(Int32Type,   Int32Type),   { case Seq(a, b) => LessThan(a, b)   }),
        nonTerminal(List(Int32Type,   Int32Type),   { case Seq(a, b) => LessEquals(a, b) }),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a, b) => LessThan(a, b)   }),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a, b) => LessEquals(a, b) })
      )
    case Int32Type =>
      List(
        terminal(IntLiteral(0), Tags.Zero),
        terminal(IntLiteral(1), Tags.One ),
        nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => plus(a, b)  }, Tags.Plus ),
        nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => minus(a, b) }, Tags.Minus),
        nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => times(a, b) }, Tags.Times)
      )

    case IntegerType =>
      List(
        terminal(InfiniteIntegerLiteral(0), Tags.Zero),
        terminal(InfiniteIntegerLiteral(1), Tags.One ),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => plus(a, b)  }, Tags.Plus ),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => minus(a, b) }, Tags.Minus),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => times(a, b) }, Tags.Times)//,
        //nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => Modulo(a, b)   }, Tags.Mod),
        //nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => Division(a, b) }, Tags.Div)
      )

    case TupleType(stps) =>
      List(
        nonTerminal(stps, Tuple, Tags.Constructor(isTerminal = false))
      )

    case cct: CaseClassType =>
      List(
        nonTerminal(cct.fields.map(_.getType), CaseClass(cct, _), Tags.tagOf(cct) )
      )

    case act: AbstractClassType =>
      act.knownCCDescendants.map { cct =>
        nonTerminal(cct.fields.map(_.getType), CaseClass(cct, _), Tags.tagOf(cct) )
      }

    case st @ SetType(base) =>
      List(
        terminal(FiniteSet(Set(), base), Tags.Constant),
        nonTerminal(List(base),   { case elems     => FiniteSet(elems.toSet, base) }, Tags.Constructor(isTerminal = false)),
        nonTerminal(List(st, st), { case Seq(a, b) => SetUnion(a, b) }),
        nonTerminal(List(st, st), { case Seq(a, b) => SetIntersection(a, b) }),
        nonTerminal(List(st, st), { case Seq(a, b) => SetDifference(a, b) })
      )

    case UnitType =>
      List(
        terminal(UnitLiteral(), Tags.Constant)
      )

    case _ =>
      Nil
  }
}
