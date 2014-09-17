/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Definitions.TypedFunDef
import purescala.TypeTrees.TypeTree

sealed abstract class TemplateInfo[T]

case class TemplateCallInfo[T](tfd: TypedFunDef, args: Seq[T]) extends TemplateInfo[T] {
  override def toString = {
    tfd.signature+args.mkString("(", ", ", ")")
  }
}

case class TemplateAppInfo[T](template: LambdaTemplate[T], b: T, args: Seq[T]) extends TemplateInfo[T] {
  override def toString = {
    template.id + "|" + b + "|" + args.mkString("(", ",", ")")
  }
}
