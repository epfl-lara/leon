/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Definitions.TypedFunDef
import purescala.Types.TypeTree

case class TemplateCallInfo[T](tfd: TypedFunDef, args: Seq[T]) {
  override def toString = {
    tfd.signature+args.mkString("(", ", ", ")")
  }
}

case class TemplateAppInfo[T](template: LambdaTemplate[T], equals: T, args: Seq[T]) {
  override def toString = {
    template.id + "|" + equals + args.mkString("(", ",", ")")
  }
}
