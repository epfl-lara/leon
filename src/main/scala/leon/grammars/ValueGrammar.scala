/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions.ValDef
import purescala.Types._
import purescala.Expressions._

/** A grammar of values (ground terms) */
case object ValueGrammar extends SimpleExpressionGrammar {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = t match {
    case BooleanType =>
      List(
        terminal(BooleanLiteral(true), Tags.One),
        terminal(BooleanLiteral(false), Tags.Zero)
      )
    case Int32Type =>
      List(
        terminal(IntLiteral(0), Tags.Zero),
        terminal(IntLiteral(1), Tags.One),
        terminal(IntLiteral(5), Tags.Constant)
      )
    case IntegerType =>
      List(
        terminal(InfiniteIntegerLiteral(0), Tags.Zero),
        terminal(InfiniteIntegerLiteral(1), Tags.One),
        terminal(InfiniteIntegerLiteral(5), Tags.Constant)
      )
    case CharType =>
      List(
        terminal(CharLiteral('a'), Tags.Constant),
        terminal(CharLiteral('b'), Tags.Constant),
        terminal(CharLiteral('0'), Tags.Constant)
      )
    case RealType =>
      List(
        terminal(FractionalLiteral(0, 1), Tags.Zero),
        terminal(FractionalLiteral(1, 1), Tags.One),
        terminal(FractionalLiteral(-1, 2), Tags.Constant),
        terminal(FractionalLiteral(555, 42), Tags.Constant)
      )
    case StringType =>
      List(
        terminal(StringLiteral(""), Tags.Constant),
        terminal(StringLiteral("a"), Tags.Constant),
        terminal(StringLiteral("foo"), Tags.Constant),
        terminal(StringLiteral("bar"), Tags.Constant)
      )

    case tp: TypeParameter =>
      List(
        terminal(GenericValue(tp, 0))
      )

    case TupleType(stps) =>
      List(
        nonTerminal(stps, Tuple, Tags.Constructor(stps.isEmpty))
      )

    case cct: CaseClassType =>
      List(
        nonTerminal(cct.fields.map(_.getType), CaseClass(cct, _), Tags.tagOf(cct))
      )

    case act: AbstractClassType =>
      act.knownCCDescendants.map { cct =>
        nonTerminal(cct.fields.map(_.getType), CaseClass(cct, _), Tags.tagOf(cct))
      }

    case st @ SetType(base) =>
      List(
        terminal(FiniteSet(Set(), base), Tags.Constant),
        nonTerminal(List(base),       { elems => FiniteSet(elems.toSet, base) }, Tags.Constructor(isTerminal = false)),
        nonTerminal(List(base, base), { elems => FiniteSet(elems.toSet, base) }, Tags.Constructor(isTerminal = false))
      )
    
    case UnitType =>
      List(
        terminal(UnitLiteral(), Tags.Constant)
      )

    case FunctionType(from, to) =>
      val args = from map (tp => ValDef(FreshIdentifier("x", tp, true)))
      List(
        nonTerminal(Seq(to), { case Seq(e) => Lambda(args, e) })
      )

    case _ =>
      Nil
  }
}
