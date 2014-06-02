/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common.Identifier
import purescala.Trees.Expr

trait TemplateEncoder[T] {
  def encodeId(id: Identifier): T
  def encodeExpr(bindings: Map[Identifier, T])(e: Expr): T
  def substitute(map: Map[T, T]): T => T

  // Encodings needed for unrollingbank
  def not(v: T): T
  def implies(l: T, r: T): T
}
