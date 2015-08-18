/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Constructors._

import bonsai._

case class EqualityGrammar(types: Set[TypeTree]) extends ExpressionGrammar[TypeTree] {
  override def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Gen] = t match {
    case BooleanType =>
      types.toList map { tp =>
        nonTerminal(List(tp, tp), { case Seq(a, b) => equality(a, b) })
      }

    case _ => Nil
  }
}
