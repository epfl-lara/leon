/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import purescala.Trees._


trait Transformer {
  def transform(e: Expr): Expr
}
