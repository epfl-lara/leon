package cp

import purescala.Trees._

/** A converter has functions for converting FunCheck expressions into Scala
 * values */
class Converter(expr2scala : (Expr => Any)) {
  def exprSeq2scala1[A](exprs: Seq[Expr]) : A =
    expr2scala(exprs(0)).asInstanceOf[A]

  def exprSeq2scala2[A,B](exprs: Seq[Expr]) : (A,B) =
    (expr2scala(exprs(0)).asInstanceOf[A], expr2scala(exprs(1)).asInstanceOf[B])
}
