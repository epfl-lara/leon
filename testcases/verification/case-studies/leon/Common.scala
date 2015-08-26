/* Copyright 2009-2015 EPFL, Lausanne */

package leon.reflect.purescala

import leon._
import collection._
import lang._
import string._

import Expressions.Variable
import Types._

object Common {

  // the type is left blank (Untyped) for Identifiers that are not variables
  case class Identifier (name: String, globalId: Int, id: Int, tpe: TypeTree, alwaysShowUniqueID: Boolean = false) {

    val getType = tpe

    def toVariable : Variable = Variable(this)

    def freshen: Identifier = FreshIdentifier(name, tpe, alwaysShowUniqueID)

  }
}
 
object FreshIdentifier {
  import Common._ 
  /** Builds a fresh identifier
    * @param name The name of the identifier
    * @param tpe The type of the identifier
    * @param alwaysShowUniqueID If the unique ID should always be shown */
  def apply(name: String, tpe: TypeTree = Untyped, alwaysShowUniqueID: Boolean = false) : Identifier = 
    new Identifier(name, UniqueCounter.nextGlobal, UniqueCounter.next(name), tpe: TypeTree, alwaysShowUniqueID)

  /** Builds a fresh identifier, whose ID is always shown
    * @param name The name of the identifier
    * @param forceId The forced ID of the identifier
    * @param tpe The type of the identifier */
  def apply(name: String, forceId: Int, tpe: TypeTree): Identifier = 
    new Identifier(name, UniqueCounter.nextGlobal, forceId, tpe, true)

}

 
object UniqueCounter {
  /*private var globalId = -1
  private var nameIds = Map[String, Int]().withDefaultValue(-1)
  */
  
  def next(name: String): Int = 0 /*synchronized {
    nameIds += name -> (1+nameIds(name))
    nameIds(name)
  }*/

  def nextGlobal = 0 /*synchronized {
    globalId += 1
    globalId
  }*/
}

