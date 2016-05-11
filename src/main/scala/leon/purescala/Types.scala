/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Common._
import Expressions._
import Definitions._
import TypeOps._

object Types {

  trait Typed extends Printable {
    val getType: TypeTree
    def isTyped : Boolean = getType != Untyped
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

    // Checks whether the subtypes of this type contain Untyped,
    // and if so sets this to Untyped.
    // Assumes the subtypes are correctly formed, so it does not descend 
    // deep into the TypeTree.
    def unveilUntyped: TypeTree = this match {
      case NAryType(tps, _) => 
        if (tps contains Untyped) Untyped else this
    }
  }

  case object Untyped extends TypeTree
  case object BooleanType extends TypeTree
  case object UnitType extends TypeTree
  case object CharType extends TypeTree
  case object IntegerType extends TypeTree
  case object RealType extends TypeTree

  abstract class BitVectorType(val size: Int) extends TypeTree
  case object Int32Type extends BitVectorType(32)
  case object StringType extends TypeTree

  class TypeParameter private (name: String) extends TypeTree {
    val id = FreshIdentifier(name, this)
    def freshen = new TypeParameter(name)

    override def equals(that: Any) = that match {
      case TypeParameter(id) => this.id == id
      case _ => false
    }

    override def hashCode = id.hashCode
  }

  object TypeParameter {
    def unapply(tp: TypeParameter): Option[Identifier] = Some(tp.id)
    def fresh(name: String) = new TypeParameter(name)
  }

  /* 
   * If you are not sure about the requirement, 
   * you should use tupleTypeWrap in purescala.Constructors
   */
  case class TupleType(bases: Seq[TypeTree]) extends TypeTree {
    val dimension: Int = bases.length
    require(dimension >= 2)
  }

  case class SetType(base: TypeTree) extends TypeTree
  case class BagType(base: TypeTree) extends TypeTree
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
      val tmap = (classDef.typeArgs zip tps).toMap
      if (tmap.isEmpty) {
        classDef.fields
      } else {
        // !! WARNING !!
        // vd.id changes but this should not be an issue as selector uses
        // classDef.params ids which do not change!
        classDef.fields.map { vd =>
          val newTpe = instantiateType(vd.getType, tmap)
          val newId = FreshIdentifier(vd.id.name, newTpe).copiedFrom(vd.id)
          vd.copy(id = newId).setPos(vd)
        }
      }
    }

    def invariant = classDef.invariant.map(_.typed(tps))

    def knownDescendants = classDef.knownDescendants.map( _.typed(tps) )

    def knownCCDescendants: Seq[CaseClassType] = classDef.knownCCDescendants.map( _.typed(tps) )

    lazy val fieldsTypes = fields.map(_.getType)

    lazy val root: ClassType = parent.map{ _.root }.getOrElse(this)

    lazy val parent = classDef.parent.map { pct =>
      instantiateType(pct, (classDef.typeArgs zip tps).toMap) match {
        case act: AbstractClassType  => act
        case t => throw LeonFatalError("Unexpected translated parent type: "+t)
      }
    }

  }

  case class AbstractClassType(classDef: AbstractClassDef, tps: Seq[TypeTree]) extends ClassType
  case class CaseClassType(classDef: CaseClassDef, tps: Seq[TypeTree]) extends ClassType

  object NAryType extends TreeExtractor[TypeTree] {
    def unapply(t: TypeTree): Option[(Seq[TypeTree], Seq[TypeTree] => TypeTree)] = t match {
      case CaseClassType(ccd, ts) => Some((ts, ts => CaseClassType(ccd, ts)))
      case AbstractClassType(acd, ts) => Some((ts, ts => AbstractClassType(acd, ts)))
      case TupleType(ts) => Some((ts, TupleType))
      case ArrayType(t) => Some((Seq(t), ts => ArrayType(ts.head)))
      case SetType(t) => Some((Seq(t), ts => SetType(ts.head)))
      case BagType(t) => Some((Seq(t), ts => BagType(ts.head)))
      case MapType(from,to) => Some((Seq(from, to), t => MapType(t(0), t(1))))
      case FunctionType(fts, tt) => Some((tt +: fts, ts => FunctionType(ts.tail.toList, ts.head)))
      /* nullary types */
      case t => Some(Nil, _ => t)
    }
  }

  object FirstOrderFunctionType {
    def unapply(tpe: TypeTree): Option[(Seq[TypeTree], TypeTree)] = tpe match {
      case FunctionType(from, to) =>
        unapply(to).map(p => (from ++ p._1) -> p._2) orElse Some(from -> to)
      case _ => None
    }
  }
  
  def optionToType(tp: Option[TypeTree]) = tp getOrElse Untyped

}
