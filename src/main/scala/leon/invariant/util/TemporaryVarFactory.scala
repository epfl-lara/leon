package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import scala.collection.mutable.{ Set => MutableSet, Map => MutableMap }

object TVarFactory {

  val temporaries = MutableSet[Identifier]()
  //these are dummy identifiers used in 'CaseClassSelector' conversion
  val dummyIds = MutableSet[Identifier]()

  def createTemp(name: String, tpe: TypeTree = Untyped): Identifier = {
    val freshid = FreshIdentifier(name, tpe, true)
    temporaries.add(freshid)
    freshid
  }

  def createDummy(tpe: TypeTree): Identifier = {
    val freshid = FreshIdentifier("dy", tpe, true)
    dummyIds.add(freshid)
    freshid
  }

  def isTemporary(id: Identifier): Boolean = temporaries.contains(id)
  def isDummy(id: Identifier): Boolean = dummyIds.contains(id)
}
