/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import utils._
import Expressions.Variable
import Types._
import Definitions.Program

object Common {


  abstract class Tree extends Positioned with Serializable with Printable {
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

    override def toString = asString(LeonContext.printNames)
  }

  /** Represents a unique symbol in Leon.
    *
    * The name is stored in the decoded (source code) form rather than encoded (JVM) form.
    * The type may be left blank (Untyped) for Identifiers that are not variables.
    */
  class Identifier private[Common](
    val name: String,
    val globalId: Int,
    private[Common] val id: Int,
    private val tpe: TypeTree,
    private val alwaysShowUniqueID: Boolean = false
  ) extends Tree with Typed with Ordered[Identifier] {

    self: Serializable =>

    val getType = tpe

    override def equals(other: Any): Boolean = other match {
      case null => false
      case i: Identifier => i.globalId == this.globalId
      case _ => false
    }

    override def hashCode: Int = globalId

    override def toString: String = {
      if (alwaysShowUniqueID) {
        name + (if (id > 0) id else "")
      } else {
        name
      }
    }

    def uniqueNameDelimited(delim: String) = name + delim + id

    def uniqueName: String = uniqueNameDelimited("")

    def toVariable: Variable = Variable(this)

    def freshen: Identifier = FreshIdentifier(name, tpe, alwaysShowUniqueID).copiedFrom(this)

    override def compare(that: Identifier): Int = {
      val ord = implicitly[Ordering[(String, Int, Int)]]
      ord.compare(
        (this.name, this.id, this.globalId),
        (that.name, that.id, that.globalId)
      )
    }
  }

  object FreshIdentifier {

    private val uniqueCounter = new UniqueCounter[String]()

    // Replace $opcode inside a string with the symbolic operator name
    private def decode(s: String) =
      scala.reflect.NameTransformer.decode(s)

    /** Builds a fresh identifier
      *
      * @param name The name of the identifier
      * @param tpe The type of the identifier
      * @param alwaysShowUniqueID If the unique ID should always be shown
      */
    def apply(name: String, tpe: TypeTree = Untyped, alwaysShowUniqueID: Boolean = false) : Identifier = 
      new Identifier(decode(name), uniqueCounter.nextGlobal, uniqueCounter.next(name), tpe, alwaysShowUniqueID)

    /** Builds a fresh identifier, whose ID is always shown
      *
      * @param name The name of the identifier
      * @param forceId The forced ID of the identifier
      * @param tpe The type of the identifier
      */
    def apply(name: String, forceId: Int, tpe: TypeTree): Identifier = 
      new Identifier(decode(name), uniqueCounter.nextGlobal, forceId, tpe, alwaysShowUniqueID =  true)

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
