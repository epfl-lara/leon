/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

/** The empty expression grammar */
case class Empty() extends ExpressionGrammar {
  val staticProductions = Map[Label, Seq[Prod]]()
  val genericProductions = Nil
}
