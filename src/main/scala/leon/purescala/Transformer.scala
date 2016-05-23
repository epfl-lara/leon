/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import purescala.Expressions.Expr

trait Transformer {
  def transform(e: Expr): Expr
}
