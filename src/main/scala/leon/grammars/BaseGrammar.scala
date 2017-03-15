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

  def generateSimpleProductions(implicit ctx: LeonContext) = {
    List(
      sTerminal(BooleanType, BooleanLiteral(false), Tags.BooleanC),
      sTerminal(BooleanType, BooleanLiteral(true),  Tags.BooleanC),
      sNonTerminal(BooleanType, List(BooleanType), { case Seq(a) => not(a) }, Tags.Not),
      sNonTerminal(BooleanType, List(BooleanType, BooleanType), { case Seq(a, b) => and(a, b) }, Tags.And),
      sNonTerminal(BooleanType, List(BooleanType, BooleanType), { case Seq(a, b) => or(a, b)  }, Tags.Or ),
      sNonTerminal(BooleanType, List(Int32Type,   Int32Type),   { case Seq(a, b) => LessThan(a, b)   }),
      sNonTerminal(BooleanType, List(Int32Type,   Int32Type),   { case Seq(a, b) => LessEquals(a, b) }),
      sNonTerminal(BooleanType, List(IntegerType, IntegerType), { case Seq(a, b) => LessThan(a, b)   }),
      sNonTerminal(BooleanType, List(IntegerType, IntegerType), { case Seq(a, b) => LessEquals(a, b) }),

      sTerminal(Int32Type, IntLiteral(0), Tags.Zero),
      sTerminal(Int32Type, IntLiteral(1), Tags.One ),
      sNonTerminal(Int32Type, List(Int32Type, Int32Type), { case Seq(a,b) => plus(a, b)  }, Tags.Plus ),
      sNonTerminal(Int32Type, List(Int32Type, Int32Type), { case Seq(a,b) => minus(a, b) }, Tags.Minus),
      sNonTerminal(Int32Type, List(Int32Type, Int32Type), { case Seq(a,b) => times(a, b) }, Tags.Times),

      sTerminal(IntegerType, InfiniteIntegerLiteral(0), Tags.Zero),
      sTerminal(IntegerType, InfiniteIntegerLiteral(1), Tags.One ),
      sNonTerminal(IntegerType, List(IntegerType, IntegerType), { case Seq(a,b) => plus(a, b)  }, Tags.Plus ),
      sNonTerminal(IntegerType, List(IntegerType, IntegerType), { case Seq(a,b) => minus(a, b) }, Tags.Minus),
      sNonTerminal(IntegerType, List(IntegerType, IntegerType), { case Seq(a,b) => times(a, b) }, Tags.Times)
    )
  }
}
