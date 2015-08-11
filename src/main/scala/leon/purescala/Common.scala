/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import utils._
import Expressions.Variable
import Types._
import Definitions.Program

object Common {


  abstract class Tree extends Positioned with Serializable {
    def copiedFrom(o: Tree): this.type = {
      setPos(o)
      this
    }

    // @EK: toString is considered harmful for non-internal things. Use asString(ctx) instead.

    def asString(implicit ctx: LeonContext): String = {
      ScalaPrinter(this, ctx)
    }

    def asString(pgm: Program)(implicit ctx: LeonContext): String = {
      ScalaPrinter(this, ctx, pgm)
    }
  }

  // the type is left blank (Untyped) for Identifiers that are not variables
  class Identifier private[Common](val name: String, val globalId: Int, val id: Int, val tpe: TypeTree, alwaysShowUniqueID: Boolean = false) extends Tree with Typed {
    self : Serializable =>

    val getType = tpe

    override def equals(other: Any): Boolean = other match {
      case null => false
      case i: Identifier => i.globalId == this.globalId
      case _ => false
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

    def freshen: Identifier = FreshIdentifier(name, tpe, alwaysShowUniqueID).copiedFrom(this)

  }

  implicit object IdentifierOrdering extends Ordering[Identifier] {
    def compare(a: Identifier, b: Identifier) = {
      val ord = implicitly[Ordering[Tuple3[String, Int, Int]]]

      ord.compare((a.name, a.id, a.globalId),
                  (b.name, b.id, b.globalId))
    }
  }

  private object UniqueCounter {
    private var globalId = -1
    private var nameIds = Map[String, Int]().withDefaultValue(-1)

    def next(name: String): Int = synchronized {
      nameIds += name -> (1+nameIds(name))
      nameIds(name)
    }

    def nextGlobal = synchronized {
      globalId += 1
      globalId
    }
  }

  object FreshIdentifier {
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

  def aliased(id1 : Identifier, id2 : Identifier) = {
    id1.toString == id2.toString
  }

  def aliased(ids1 : Set[Identifier], ids2 : Set[Identifier]) = {
    val s1 = ids1.groupBy{ _.toString }.keySet
    val s2 = ids2.groupBy{ _.toString }.keySet
    (s1 & s2).nonEmpty
  }

}
