/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import purescala.Common._
import purescala.Types._
import scala.collection.mutable.{ Set => MutableSet, Map => MutableMap}

object TVarFactory {

  type Context = Int
  val temporaries = MutableMap[Context, MutableSet[Identifier]]()
  private var context: Context = 0

  def newContext = {
    context += 1
    temporaries += (context -> MutableSet())
    context
  }
  val defaultContext = newContext

  def createTemp(name: String, tpe: TypeTree = Untyped, context: Context): Identifier = {
    val freshid = FreshIdentifier(name, tpe, true)
    temporaries(context) += freshid
    freshid
  }

  def createTempDefault(name: String, tpe: TypeTree = Untyped): Identifier = {
    val freshid = FreshIdentifier(name, tpe, true)
    temporaries(defaultContext) += freshid
    freshid
  }

  def isTemp(id: Identifier, context: Context): Boolean =
    temporaries.contains(context) && temporaries(context)(id)
}
