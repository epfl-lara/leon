/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Constructors._

/** A grammar of equalities
  *
  * @param types The set of types for which equalities will be generated
  */
case class EqualityGrammar(types: Set[TypeTree]) extends SimpleExpressionGrammar {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = t match {
    case BooleanType =>
      types.toList map { tp =>
        nonTerminal(List(tp, tp), { case Seq(a, b) => equality(a, b) }, Tags.Equals)
      }

    case _ => Nil
  }
}
