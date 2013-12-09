package leon
package purescala 

import Trees._
import Common._
import TreeOps._

object NonDeterminismExtension {
  
  val nondetIdName = "nondet"
  def nondetId : Identifier = FreshIdentifier(nondetIdName,false)
  
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
