/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common.Identifier
import purescala.Expressions.Expr

trait TemplateEncoder[T] {
  def encodeId(id: Identifier): T
  def encodeExpr(bindings: Map[Identifier, T])(e: Expr): T
  def substitute(map: Map[T, T]): T => T

  // Encodings needed for unrollingbank
  def mkNot(v: T): T
  def mkOr(ts: T*): T
  def mkAnd(ts: T*): T
  def mkEquals(l: T, r: T): T
  def mkImplies(l: T, r: T): T
}
