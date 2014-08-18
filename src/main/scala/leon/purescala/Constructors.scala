/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import utils._

object Constructors {
  import Trees._
  import Common._

  def tupleSelect(t: Expr, index: Int) = t match {
    case Tuple(es) =>
      es(index-1)
    case _ =>
      TupleSelect(t, index)
  }

  def letTuple(binders: Seq[Identifier], value: Expr, body: Expr) = binders match {
    case Nil =>
      body
    case x :: Nil =>
      Let(x, tupleSelect(value, 1), body)
    case xs =>
      LetTuple(xs, value, body)
  }

  def tupleChoose(ch: Choose): Expr = {
    if (ch.vars.size > 1) {
      ch
    } else {
      Tuple(Seq(ch))
    }
  }
}
