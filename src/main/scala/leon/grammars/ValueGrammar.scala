/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Expressions._

case object ValueGrammar extends ExpressionGrammar[TypeTree] {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Gen] = t match {
    case BooleanType =>
      List(
        terminal(BooleanLiteral(true)),
        terminal(BooleanLiteral(false))
      )
    case Int32Type =>
      List(
        terminal(IntLiteral(0)),
        terminal(IntLiteral(1)),
        terminal(IntLiteral(5))
      )
    case IntegerType =>
      List(
        terminal(InfiniteIntegerLiteral(0)),
        terminal(InfiniteIntegerLiteral(1)),
        terminal(InfiniteIntegerLiteral(5))
      )
    case StringType =>
      List(
        terminal(StringLiteral("")),
        terminal(StringLiteral("a")),
        terminal(StringLiteral("\"'\n\r\t")),
        terminal(StringLiteral("Lara 2007"))
      )

    case tp: TypeParameter =>
      for (ind <- (1 to 3).toList) yield {
        terminal(GenericValue(tp, ind))
      }

    case TupleType(stps) =>
      List(
        nonTerminal(stps, { sub => Tuple(sub) })
      )

    case cct: CaseClassType =>
      List(
        nonTerminal(cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)})
      )

    case act: AbstractClassType =>
      act.knownCCDescendants.map { cct =>
        nonTerminal(cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)})
      }

    case st @ SetType(base) =>
      List(
        nonTerminal(List(base),       { case elems => FiniteSet(elems.toSet, base) }),
        nonTerminal(List(base, base), { case elems => FiniteSet(elems.toSet, base) })
      )
    
    case UnitType =>
      List(
        terminal(UnitLiteral())
      )

    case _ =>
      Nil
  }
}
