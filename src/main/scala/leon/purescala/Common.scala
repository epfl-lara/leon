/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import utils._
import Expressions.Variable
import Types._
import Definitions.Definition

object Common {


  abstract class Tree extends Positioned with Serializable {
    def copiedFrom(o: Tree): this.type = {
      setPos(o)
      this
    }

    override def toString: String = PrettyPrinter(this)

    def asString(implicit ctx: LeonContext): String = {
      ScalaPrinter(this, ctx)
    }
  }

  // the type is left blank (Untyped) for Identifiers that are not variables
  class Identifier private[Common](val name: String, val globalId: Int, val id: Int, val tpe: TypeTree, alwaysShowUniqueID: Boolean = false) extends Tree with Typed {
    self : Serializable =>

    val getType = tpe

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

    def freshen: Identifier = FreshIdentifier(name, tpe, alwaysShowUniqueID).copiedFrom(this)
    
    var owner : Option[Definition] = None
    
    def setOwner(df : Definition) : Identifier = { this.owner = Some(df); this }
    
    def ownerChain : List[Identifier] = owner match { 
      case None => List(this)
      case Some(ow) => ow.id :: ow.id.ownerChain
    }

    def fullName: String = (ownerChain.map(_.name) :+ name).mkString(".")

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
    def apply(name: String, tpe: TypeTree = Untyped, alwaysShowUniqueID: Boolean = false) : Identifier = 
      new Identifier(name, UniqueCounter.nextGlobal, UniqueCounter.next(name), tpe: TypeTree, alwaysShowUniqueID)

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
