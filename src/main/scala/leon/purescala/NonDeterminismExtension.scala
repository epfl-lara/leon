package leon
package purescala 

import Trees._
import Common._
import TreeOps._
import leon.plugin.NondeterminismConverter
import Definitions._

object NondeterminismExtension {
  
  val nondetIdName = "nondet"
  //do not make this def a val as we need avoid certain accidental optimizations from being
  //applied to the nondetIds
  def nondetId : Identifier = FreshIdentifier(nondetIdName,false)
  
  def isNonDetId(id: Identifier) = (id.name == nondetIdName) 
  
  def hasNondet(e: Expr) : Boolean = {
    variablesOf(e).exists((id: Identifier) => id.name == nondetIdName)
  }
  
  /**
   * Replaces every nondetId by a fresh Identifier
   */
  def makeUniqueNondetIds(expr : Expr) : Expr = { 
    simplePostTransform((e: Expr) => e match {
      case Variable(id) if(id.name == nondetIdName) => {
        FreshIdentifier(id.name, true).setType(id.getType).toVariable
      }
      case _ => e
    })(expr)
  }
}
