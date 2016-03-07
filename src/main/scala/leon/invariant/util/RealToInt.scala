/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import invariant.factories._
import solvers._

/**
 * maps all real valued variables and literals to new integer variables/literals and
 * performs the reverse mapping
 * Note: this should preserve the template identifier property
 */
class RealToInt {

  val bone = BigInt(1)
  var realToIntId = Map[Identifier, Identifier]()
  var intToRealId = Map[Identifier, Identifier]()

  def mapRealToInt(inexpr: Expr): Expr = {
    val transformer = (e: Expr) => e match {
      case FractionalLiteral(num, `bone`) => InfiniteIntegerLiteral(num)
      case FractionalLiteral(_, _) => throw new IllegalStateException("Real literal with non-unit denominator")
      case v @ Variable(realId) if (v.getType == RealType) => {
        val newId = realToIntId.getOrElse(realId, {
          //note: the fresh identifier has to be a template identifier if the original one is a template identifier
          val freshId = if (TemplateIdFactory.IsTemplateIdentifier(realId))
            TemplateIdFactory.freshIdentifier(realId.name, IntegerType)
          else
            FreshIdentifier(realId.name, IntegerType, true)

          realToIntId += (realId -> freshId)
          intToRealId += (freshId -> realId)
          freshId
        })
        Variable(newId)
      }
      case _ => e
    }
    simplePostTransform(transformer)(inexpr)
  }

  def unmapModel(model: Model): Model = {
    new Model(model.map(pair => {
      val (key, value) = if (intToRealId.contains(pair._1)) {
        (intToRealId(pair._1),
          pair._2 match {
            case InfiniteIntegerLiteral(v) => FractionalLiteral(v.toInt, 1)
            case _ => pair._2
          })
      } else pair
      (key -> value)
    }).toMap)
  }

  def mapModel(model: Model): Model = {
    new Model(model.collect {
      case (k, FractionalLiteral(n, bone)) =>
        (realToIntId(k), InfiniteIntegerLiteral(n))
      case (k, v) =>
        if (realToIntId.contains(k)) {
          (realToIntId(k), v)
        } else {
          (k, v)
        }
    }.toMap)
  }
}