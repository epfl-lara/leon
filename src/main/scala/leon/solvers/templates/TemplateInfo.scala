/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Definitions.TypedFunDef
import Template.Arg

case class TemplateCallInfo[T](tfd: TypedFunDef, args: Seq[Arg[T]]) {
  override def toString = {
    tfd.signature + args.map {
      case Right(m) => m.toString
      case Left(v) => v.toString
    }.mkString("(", ", ", ")")
  }
}

case class TemplateAppInfo[T](template: LambdaTemplate[T], equals: T, args: Seq[Arg[T]]) {
  override def toString = {
    template.ids._2 + "|" + equals + args.map {
      case Right(m) => m.toString
      case Left(v) => v.toString
    }.mkString("(", ",", ")")
  }
}
