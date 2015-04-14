/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import purescala.Expressions._

trait Transformer {
  def transform(e: Expr): Expr
}
