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

  protected[grammars] def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = t match {
    case BooleanType =>
      List(
        terminal(BooleanLiteral(false), classOf[BooleanLiteral], Tags.BooleanC),
        terminal(BooleanLiteral(true), classOf[BooleanLiteral],  Tags.BooleanC),
        nonTerminal(List(BooleanType), { case Seq(a) => not(a) }, classOf[Not], Tags.Not),
        nonTerminal(List(BooleanType, BooleanType), { case Seq(a, b) => and(a, b) }, classOf[And], Tags.And),
        nonTerminal(List(BooleanType, BooleanType), { case Seq(a, b) => or(a, b)  }, classOf[Or], Tags.Or ),
        nonTerminal(List(Int32Type,   Int32Type),   { case Seq(a, b) => LessThan(a, b)   }, classOf[LessThan]),
        nonTerminal(List(Int32Type,   Int32Type),   { case Seq(a, b) => LessEquals(a, b) }, classOf[LessEquals]),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a, b) => LessThan(a, b)   }, classOf[LessThan]),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a, b) => LessEquals(a, b) }, classOf[LessEquals])
      )
    case Int32Type =>
      List(
        terminal(IntLiteral(0), classOf[IntLiteral], Tags.Zero),
        terminal(IntLiteral(1), classOf[IntLiteral], Tags.One ),
        nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => plus(a, b)  }, classOf[Plus], Tags.Plus ),
        nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => minus(a, b) }, classOf[Minus], Tags.Minus),
        nonTerminal(List(Int32Type, Int32Type), { case Seq(a,b) => times(a, b) }, classOf[Times], Tags.Times)
      )

    case IntegerType =>
      List(
        terminal(InfiniteIntegerLiteral(0), classOf[InfiniteIntegerLiteral], Tags.Zero),
        terminal(InfiniteIntegerLiteral(1), classOf[InfiniteIntegerLiteral], Tags.One ),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => plus(a, b)  }, classOf[Plus], Tags.Plus ),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => minus(a, b) }, classOf[Minus], Tags.Minus),
        nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => times(a, b) }, classOf[Times], Tags.Times)//,
        //nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => Modulo(a, b)   }, classOf[Modulo], Tags.Mod),
        //nonTerminal(List(IntegerType, IntegerType), { case Seq(a,b) => Division(a, b) }, classOf[Division], Tags.Div)
      )

    case TupleType(stps) =>
      List(
        nonTerminal(stps, Tuple, classOf[Tuple], Tags.Constructor(isTerminal = false))
      )

    case cct: CaseClassType =>
      List(
        nonTerminal(cct.fields.map(_.getType), CaseClass(cct, _), classOf[CaseClass], Tags.tagOf(cct) )
      )

    case act: AbstractClassType =>
      act.knownCCDescendants.map { cct =>
        nonTerminal(cct.fields.map(_.getType), CaseClass(cct, _), classOf[CaseClass], Tags.tagOf(cct) )
      }

    case st @ SetType(base) =>
      List(
        terminal(FiniteSet(Set(), base), classOf[FiniteSet], Tags.Constant),
        nonTerminal(List(base),   { case elems     => FiniteSet(elems.toSet, base) }, classOf[FiniteSet], Tags.Constructor(isTerminal = false)),
        nonTerminal(List(st, st), { case Seq(a, b) => SetUnion(a, b) }, classOf[SetUnion]),
        nonTerminal(List(st, st), { case Seq(a, b) => SetIntersection(a, b) }, classOf[SetIntersection]),
        nonTerminal(List(st, st), { case Seq(a, b) => SetDifference(a, b) }, classOf[SetDifference])
      )

    case UnitType =>
      List(
        terminal(UnitLiteral(), classOf[UnitLiteral], Tags.Constant)
      )

    case _ =>
      Nil
  }
}
