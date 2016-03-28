/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package unrolling

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

case class TemplateAppInfo[T](template: Either[LambdaTemplate[T], T], equals: T, args: Seq[Arg[T]]) {
  override def toString = {
    val caller = template match {
      case Left(tmpl) => tmpl.ids._2
      case Right(c) => c
    }

    caller + "|" + equals + args.map {
      case Right(m) => m.toString
      case Left(v) => v.toString
    }.mkString("(", ",", ")")
  }
}

object TemplateAppInfo {
  def apply[T](template: LambdaTemplate[T], equals: T, args: Seq[Arg[T]]): TemplateAppInfo[T] =
    TemplateAppInfo(Left(template), equals, args)

  def apply[T](caller: T, equals: T, args: Seq[Arg[T]]): TemplateAppInfo[T] =
    TemplateAppInfo(Right(caller), equals, args)
}
