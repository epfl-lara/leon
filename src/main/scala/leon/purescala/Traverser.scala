/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

import purescala.Trees._

trait Traverser[T] {
  def traverse(e: Expr): T
}
