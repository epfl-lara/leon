/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Expressions._

abstract class RewritingSolver[+S <: Solver, T](underlying: S) {
  val context = underlying.context

  /** The type T is used to encode any meta information useful, for instance, to reconstruct
    * models. */
  def rewriteCnstr(expression : Expr) : (Expr,T)

  def reconstructModel(model : Map[Identifier,Expr], meta : T) : Map[Identifier,Expr]

  private var storedMeta : List[T] = Nil

  def assertCnstr(expression : Expr) {
    val (rewritten, meta) = rewriteCnstr(expression)
    storedMeta = meta :: storedMeta
    underlying.assertCnstr(rewritten)
  }

  def getModel : Map[Identifier,Expr] = {
    storedMeta match {
      case Nil    => underlying.getModel
      case m :: _ => reconstructModel(underlying.getModel, m)
    }
  }
}
