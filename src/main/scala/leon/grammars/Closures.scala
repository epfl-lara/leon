/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Common._

case object Closures extends ExpressionGrammar {
  def computeProductions(lab: Label)(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]] = lab.getType match {
    case FunctionType(argsTpes, ret) =>
      val args = argsTpes.zipWithIndex.map { case (tpe, i) =>
        ValDef(FreshIdentifier("a"+i, tpe))
      }

      val rlab = Label(ret).withAspect(aspects.ExtraTerminals(args.map(_.toVariable).toSet))

      List(
        ProductionRule[Label, Expr](List(rlab), { case Seq(body) => Lambda(args, body) }, Tags.Top, 1, 1.0)
      )

    case _ =>
      Nil
  }
}
