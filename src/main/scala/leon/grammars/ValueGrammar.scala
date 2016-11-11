/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions.ValDef
import purescala.Types._
import purescala.Expressions._

case object ValueGrammar extends ValueGrammar

/** A grammar of values (ground terms) */
abstract class ValueGrammar extends SimpleExpressionGrammar {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = t match {
    case BooleanType =>
      List(
        terminal(BooleanLiteral(true), classOf[BooleanLiteral], Tags.One),
        terminal(BooleanLiteral(false), classOf[BooleanLiteral], Tags.Zero)
      )
    case Int32Type =>
      List(
        terminal(IntLiteral(0), classOf[IntLiteral], Tags.Zero),
        terminal(IntLiteral(1), classOf[IntLiteral], Tags.One),
        terminal(IntLiteral(5), classOf[IntLiteral], Tags.Constant),
        terminal(IntLiteral(-1), classOf[IntLiteral], Tags.Constant, 3),
        terminal(IntLiteral(2), classOf[IntLiteral],  Tags.Constant, 3),
        terminal(IntLiteral(3), classOf[IntLiteral],  Tags.Constant, 3),
        terminal(IntLiteral(-2), classOf[IntLiteral], Tags.Constant, 5),
        terminal(IntLiteral(4), classOf[IntLiteral],  Tags.Constant, 5),
        terminal(IntLiteral(10), classOf[IntLiteral], Tags.Constant, 5)
      )
    case IntegerType =>
      List(
        terminal(InfiniteIntegerLiteral(0), classOf[InfiniteIntegerLiteral], Tags.Zero),
        terminal(InfiniteIntegerLiteral(1), classOf[InfiniteIntegerLiteral], Tags.One),
        terminal(InfiniteIntegerLiteral(5), classOf[InfiniteIntegerLiteral], Tags.Constant),
        terminal(InfiniteIntegerLiteral(-1), classOf[InfiniteIntegerLiteral], Tags.Constant, 3),
        terminal(InfiniteIntegerLiteral(2), classOf[InfiniteIntegerLiteral],  Tags.Constant, 3),
        terminal(InfiniteIntegerLiteral(3), classOf[InfiniteIntegerLiteral],  Tags.Constant, 3),
        terminal(InfiniteIntegerLiteral(-2), classOf[InfiniteIntegerLiteral], Tags.Constant, 5),
        terminal(InfiniteIntegerLiteral(4), classOf[InfiniteIntegerLiteral],  Tags.Constant, 5),
        terminal(InfiniteIntegerLiteral(10), classOf[InfiniteIntegerLiteral], Tags.Constant, 5)
      )
    case CharType =>
      List(
        terminal(CharLiteral('a'), classOf[CharLiteral], Tags.Constant),
        terminal(CharLiteral('b'), classOf[CharLiteral], Tags.Constant),
        terminal(CharLiteral('0'), classOf[CharLiteral], Tags.Constant)
      )
    case RealType =>
      List(
        terminal(FractionalLiteral(0, 1), classOf[FractionalLiteral], Tags.Zero),
        terminal(FractionalLiteral(1, 1), classOf[FractionalLiteral], Tags.One),
        terminal(FractionalLiteral(-1, 2), classOf[FractionalLiteral], Tags.Constant),
        terminal(FractionalLiteral(555, 42), classOf[FractionalLiteral], Tags.Constant)
      )
    case StringType =>
      List(
        terminal(StringLiteral(""), classOf[StringLiteral], Tags.Constant),
        terminal(StringLiteral("a"), classOf[StringLiteral], Tags.Constant),
        terminal(StringLiteral("foo"), classOf[StringLiteral], Tags.Constant),
        terminal(StringLiteral("bar"), classOf[StringLiteral], Tags.Constant),
        terminal(StringLiteral("b"), classOf[StringLiteral], Tags.Constant, 3),
        terminal(StringLiteral("c"), classOf[StringLiteral], Tags.Constant, 3),
        terminal(StringLiteral("d"), classOf[StringLiteral], Tags.Constant, 3)
      )

    case tp: TypeParameter =>
      List(
        terminal(GenericValue(tp, 0), classOf[GenericValue])
      )

    case TupleType(stps) =>
      List(
        nonTerminal(stps, Tuple, classOf[Tuple], Tags.Constructor(stps.isEmpty))
      )

    case cct: CaseClassType =>
      List(
        nonTerminal(cct.fields.map(_.getType), CaseClass(cct, _), classOf[CaseClass], Tags.tagOf(cct))
      )

    case act: AbstractClassType =>
      act.knownCCDescendants.map { cct =>
        nonTerminal(cct.fields.map(_.getType), CaseClass(cct, _), classOf[CaseClass], Tags.tagOf(cct))
      }

    case st @ SetType(base) =>
      List(
        terminal(FiniteSet(Set(), base), classOf[FiniteSet], Tags.Constant),
        nonTerminal(List(base),       { elems => FiniteSet(elems.toSet, base) }, classOf[FiniteSet], Tags.Constructor(isTerminal = false)),
        nonTerminal(List(base, base), { elems => FiniteSet(elems.toSet, base) }, classOf[FiniteSet], Tags.Constructor(isTerminal = false))
      )
    
    case UnitType =>
      List(
        terminal(UnitLiteral(), classOf[UnitLiteral], Tags.Constant)
      )

    case FunctionType(from, to) =>
      val args = from map (tp => ValDef(FreshIdentifier("x", tp, true)))
      List(
        nonTerminal(Seq(to), { case Seq(e) => Lambda(args, e) }, classOf[Lambda])
      )

    case _ =>
      Nil
  }
}
