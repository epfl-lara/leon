/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Definitions.TypedFunDef

case class TemplateCallInfo[T](tfd: TypedFunDef, args: Seq[T]) {
  override def toString = {
    tfd.signature+args.mkString("(", ", ", ")")
  }
}
