/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Definitions._
import purescala.Expressions._
import purescala.TypeOps.instantiateType
import purescala.Common._

case class Closures(maxArgs: Int = 4) extends ExpressionGrammar {
  def generateProductions(implicit ctx: LeonContext) = {
    for (nTps <- 1 to maxArgs+1) yield {
      val tps = for (i <- 1 to nTps) yield TypeParameterDef(TypeParameter.fresh("T"+i))

      val to    = tps.head.tp
      val froms = tps.tail.map(_.tp)


      val prodBuilder = { (tmap: Map[TypeParameter, TypeTree]) =>

        val args = froms.zipWithIndex.map { case (tpe, i) =>
          ValDef(FreshIdentifier("a"+i, instantiateType(tpe, tmap)))
        }

        val rlab = Label(instantiateType(to, tmap)).withAspect(aspects.ExtraTerminals(args.map(_.toVariable).toSet))

        ProductionRule[Label, Expr](
          Seq(rlab), { case Seq(body) => Lambda(args, body) }, Tags.Top, cost = 1, logProb = -1.0
        )
      }

      GenericProdSeed(tps, Label(FunctionType(froms, to)), Seq(to),  prodBuilder)
    }
  }
}
