/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import scala.language.implicitConversions

object TypeTrees {
  import Common._
  import Trees._
  import Definitions._
  import TypeTreeOps._

  trait Typed {
    def getType: TypeTree
    def isTyped : Boolean = (getType != Untyped)
  }

  class TypeErrorException(msg: String) extends Exception(msg)

  object TypeErrorException {
    def apply(obj: Expr, exp: List[TypeTree]): TypeErrorException = {
      new TypeErrorException("Type error: "+obj+", expected: "+exp.mkString(" or ")+", found "+obj.getType)
    }

    def apply(obj: Expr, exp: TypeTree): TypeErrorException = {
      apply(obj, List(exp))
    }
  }

  abstract class TypeTree extends Tree with Typed {
    val getType = this
    def unveilUntyped: TypeTree = this match {
      case NAryType(tps, builder) => 
        val subs = tps map { _.unveilUntyped }
        if (subs contains Untyped) Untyped else builder(subs)
    }
  }

  case object Untyped extends TypeTree
  case object BooleanType extends TypeTree
  case object UnitType extends TypeTree
  case object CharType extends TypeTree
  case object IntegerType extends TypeTree

  case class BitVectorType(size: Int) extends TypeTree
  case object Int32Type extends TypeTree

  case class TypeParameter(id: Identifier) extends TypeTree {
    def freshen = TypeParameter(id.freshen)
  }

  /* 
   * If you are not sure about the requirement, 
   * you should use tupleTypeWrap in purescala.Constructors
   */
  case class TupleType (val bases: Seq[TypeTree]) extends TypeTree {
    lazy val dimension: Int = bases.length
    require(dimension >= 2)
  }

  case class SetType(base: TypeTree) extends TypeTree
  case class MultisetType(base: TypeTree) extends TypeTree
  case class MapType(from: TypeTree, to: TypeTree) extends TypeTree
  case class FunctionType(from: Seq[TypeTree], to: TypeTree) extends TypeTree
  case class ArrayType(base: TypeTree) extends TypeTree

  sealed abstract class ClassType extends TypeTree {
    val classDef: ClassDef
    val id: Identifier = classDef.id

    override def hashCode : Int = id.hashCode + tps.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : ClassType => t.id == this.id && t.tps == this.tps
      case _ => false
    }

    val tps: Seq[TypeTree]

    assert(classDef.tparams.size == tps.size)

    lazy val fields = {
      val tmap = (classDef.tparams zip tps).toMap
      if (tmap.isEmpty) {
        classDef.fields
      } else {
        // !! WARNING !!
        // vd.id.getType will NOT match vd.tpe, but we kind of need this for selectorID2Index...
        // See with Etienne about changing this!
        classDef.fields.map(vd => ValDef(vd.id, instantiateType(vd.tpe, tmap)))
      }
    }

    def knownDescendents = classDef.knownDescendents.map(classDefToClassType(_, tps))

    def knownCCDescendents = classDef.knownCCDescendents.map(CaseClassType(_, tps))

    lazy val fieldsTypes = fields.map(_.tpe)

    lazy val root = parent.getOrElse(this)

    lazy val parent = classDef.parent.map {
      pct => instantiateType(pct, (classDef.tparams zip tps).toMap) match {
        case act: AbstractClassType  => act
        case t  => throw LeonFatalError("Unexpected translated parent type: "+t)
      }
    }

  }
  case class AbstractClassType(classDef: AbstractClassDef, tps: Seq[TypeTree]) extends ClassType
  case class CaseClassType(override val classDef: CaseClassDef, tps: Seq[TypeTree]) extends ClassType

  def classDefToClassType(cd: ClassDef, tps: Seq[TypeTree]): ClassType = cd match {
    case a: AbstractClassDef => AbstractClassType(a, tps)
    case c: CaseClassDef => CaseClassType(c, tps)
  }

  // Using definition types
  def classDefToClassType(cd: ClassDef): ClassType = {
    classDefToClassType(cd, cd.tparams.map(_.tp))
  }

  object NAryType {
    def unapply(t: TypeTree): Option[(Seq[TypeTree], Seq[TypeTree] => TypeTree)] = t match {
      case CaseClassType(ccd, ts) => Some((ts, ts => CaseClassType(ccd, ts)))
      case AbstractClassType(acd, ts) => Some((ts, ts => AbstractClassType(acd, ts)))
      case TupleType(ts) => Some((ts, Constructors.tupleTypeWrap(_)))
      case ArrayType(t) => Some((Seq(t), ts => ArrayType(ts.head)))
      case SetType(t) => Some((Seq(t), ts => SetType(ts.head)))
      case MultisetType(t) => Some((Seq(t), ts => MultisetType(ts.head)))
      case MapType(from,to) => Some((Seq(from, to), t => MapType(t(0), t(1))))
      case FunctionType(fts, tt) => Some((tt +: fts, ts => FunctionType(ts.tail.toList, ts.head)))
      case t => Some(Nil, fake => t)
    }
  }
  
  implicit def optTypeToType(tp: Option[TypeTree]) = tp getOrElse Untyped

}
