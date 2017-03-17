/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions.ValDef
import purescala.Types._
import purescala.Definitions._
import purescala.Expressions._

/** A grammar of values (ground terms) */
case object Literals extends SimpleExpressionGrammar {

  def generateSimpleProductions(implicit ctx: LeonContext) = {
    List(
      sTerminal(BooleanType, BooleanLiteral(true), Tags.One),
      sTerminal(BooleanType, BooleanLiteral(false), Tags.Zero),

      sTerminal(Int32Type, IntLiteral(0),  Tags.Zero),
      sTerminal(Int32Type, IntLiteral(1),  Tags.One),
      sTerminal(Int32Type, IntLiteral(5),  Tags.Constant),
      sTerminal(Int32Type, IntLiteral(-1), Tags.Constant, 3),
      sTerminal(Int32Type, IntLiteral(2),  Tags.Constant, 3),
      sTerminal(Int32Type, IntLiteral(3),  Tags.Constant, 3),
      sTerminal(Int32Type, IntLiteral(-2), Tags.Constant, 5),
      sTerminal(Int32Type, IntLiteral(4),  Tags.Constant, 5),
      sTerminal(Int32Type, IntLiteral(10), Tags.Constant, 5),

      sTerminal(IntegerType, InfiniteIntegerLiteral(0),  Tags.Zero),
      sTerminal(IntegerType, InfiniteIntegerLiteral(1),  Tags.One),
      sTerminal(IntegerType, InfiniteIntegerLiteral(5),  Tags.Constant),
      sTerminal(IntegerType, InfiniteIntegerLiteral(-1), Tags.Constant, 3),
      sTerminal(IntegerType, InfiniteIntegerLiteral(2),  Tags.Constant, 3),
      sTerminal(IntegerType, InfiniteIntegerLiteral(3),  Tags.Constant, 3),
      sTerminal(IntegerType, InfiniteIntegerLiteral(-2), Tags.Constant, 5),
      sTerminal(IntegerType, InfiniteIntegerLiteral(4),  Tags.Constant, 5),
      sTerminal(IntegerType, InfiniteIntegerLiteral(10), Tags.Constant, 5),

      sTerminal(CharType, CharLiteral('a'), Tags.Constant),
      sTerminal(CharType, CharLiteral('b'), Tags.Constant),
      sTerminal(CharType, CharLiteral('0'), Tags.Constant),

      sTerminal(RealType, FractionalLiteral(0, 1), Tags.Zero),
      sTerminal(RealType, FractionalLiteral(1, 1), Tags.One),
      sTerminal(RealType, FractionalLiteral(-1, 2), Tags.Constant),
      sTerminal(RealType, FractionalLiteral(555, 42), Tags.Constant),

      sTerminal(StringType, StringLiteral(""), Tags.Constant),
      sTerminal(StringType, StringLiteral("a"), Tags.Constant),
      sTerminal(StringType, StringLiteral("foo"), Tags.Constant),
      sTerminal(StringType, StringLiteral("bar"), Tags.Constant),
      sTerminal(StringType, StringLiteral("b"), Tags.Constant, 3),
      sTerminal(StringType, StringLiteral("c"), Tags.Constant, 3),
      sTerminal(StringType, StringLiteral("d"), Tags.Constant, 3),

      sTerminal(UnitType, UnitLiteral(), Tags.Constant)
    )
  }
}
