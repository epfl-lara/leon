/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import purescala.Expressions._

trait Transformer {
  def transform(e: Expr): Expr
}
