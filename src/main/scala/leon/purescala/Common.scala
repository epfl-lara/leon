/* Copyright 2009-2013 EPFL, Lausanne */
package leon
package purescala

import utils._

object Common {
  import Trees.Variable
  import TypeTrees.Typed

  abstract class Tree extends Positioned with Serializable

  // the type is left blank (Untyped) for Identifiers that are not variables
  class Identifier private[Common](val name: String, private val globalId: Int, val id: Int, alwaysShowUniqueID: Boolean = false) extends Tree with Typed {
    self : Serializable =>

    override def equals(other: Any): Boolean = {
      if(other == null || !other.isInstanceOf[Identifier])
        false
      else
        other.asInstanceOf[Identifier].globalId == this.globalId
    }

    override def hashCode: Int = globalId

    override def toString: String = {
      if(alwaysShowUniqueID) {
        name + (if(id > 0) id else "")
      } else {
        name
      }
    }

    def uniqueName : String = name + id

    def toVariable : Variable = Variable(this)

    private var _islb: Boolean = false
    def markAsLetBinder : Identifier = { _islb = true; this }
    def isLetBinder : Boolean = _islb

    def freshen: Identifier = FreshIdentifier(name, alwaysShowUniqueID).setType(getType)
  }

  private object UniqueCounter {
    private var globalId = -1
    private var nameIds = Map[String, Int]().withDefaultValue(-1)

    def next(name: String): Int = {
      nameIds += name -> (1+nameIds(name))
      nameIds(name)
    }
    
    def nextGlobal = {
      globalId += 1
      globalId
    }
  }

  object FreshIdentifier {
    def apply(name: String, alwaysShowUniqueID: Boolean = false) : Identifier = new Identifier(name, UniqueCounter.nextGlobal, UniqueCounter.next(name), alwaysShowUniqueID)

    def apply(name: String, forceId: Int): Identifier = new Identifier(name, UniqueCounter.nextGlobal, forceId, true)

  }

}
