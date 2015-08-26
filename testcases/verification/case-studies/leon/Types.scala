/* Copyright 2009-2015 EPFL, Lausanne */

package leon.reflect.purescala

import scala.language.implicitConversions

import leon._
import lang._
import collection._
import string._ 

import Common._
import Expressions._
import Definitions._
//import TypeOps._

object Types {

  abstract class TypeTree {
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

  abstract class BitVectorType(val size: BigInt) extends TypeTree
  case object Int32Type extends BitVectorType(32)

  case class TypeParameter(id: Identifier) extends TypeTree {
    def freshen = TypeParameter(id.freshen)
  }

  /* 
   * If you are not sure about the requirement, 
   * you should use tupleTypeWrap in purescala.Constructors
   */
  case class TupleType (bases: List[TypeTree]) extends TypeTree {
    val dimension: BigInt = bases.length
    require(dimension >= 2)
  }

  case class SetType(base: TypeTree) extends TypeTree
  case class MapType(from: TypeTree, to: TypeTree) extends TypeTree
  case class FunctionType(from: List[TypeTree], to: TypeTree) extends TypeTree
  case class ArrayType(base: TypeTree) extends TypeTree

  abstract class ClassType extends TypeTree {
  
    val classDef: ClassDef
    val tps: List[TypeTree]

    val id: Identifier = classDef.id

    lazy val fields = { // FIXME
      //val tmap = (classDef.tparams zip tps).toMap
      //if (tmap.isEmpty) {
        classDef.fields
      //} else {
        // This is the only case where ValDef overrides the type of its Identifier
        //classDef.fields.map(vd => ValDef(vd.id, Some(instantiateType(vd.getType, tmap))))
      //}
    }

    def knownDescendants = classDef.knownDescendants.map( _.typed(tps) )

    def knownCCDescendants = classDef.knownCCDescendants.map( _.typed(tps) )

    lazy val fieldsTypes = fields.map(_.getType)

    lazy val root: ClassType = parent.map{ _.root }.getOrElse(this)

    lazy val parent = classDef.parent/* FIXME .map { pct => 
      instantiateType(pct, (classDef.tparams zip tps).toMap) match {
        case act: AbstractClassType  => act
        case t => throw LeonFatalError("Unexpected translated parent type: "+t)
      }
    }*/
  }

  case class AbstractClassType(classDef: ClassDef, tps: List[TypeTree]) extends ClassType // FIXME: ClassDef
  case class CaseClassType(classDef: ClassDef, tps: List[TypeTree]) extends ClassType     // FIXME: ClassDef

  def optionToType(tp: Option[TypeTree]) = tp getOrElse Untyped

} 

object NAryType {
  import Types._
  def unapply(t: TypeTree): Option[(List[TypeTree], List[TypeTree] => TypeTree)] = t match {
    case CaseClassType(ccd, ts) => Some((ts, ts => CaseClassType(ccd, ts)))
    case AbstractClassType(acd, ts) => Some((ts, ts => AbstractClassType(acd, ts)))
    case TupleType(ts) => Some((ts, TupleType(_))) // FIXME Constructors.tupleTypeWrap _))
    case ArrayType(t) => Some((List(t), ts => ArrayType(ts.head)))
    case SetType(t) => Some((List(t), ts => SetType(ts.head)))
    case MapType(from,to) => Some((List(from, to), t => MapType(t(0), t(1))))
    case FunctionType(fts, tt) => Some((tt :: fts, ts => FunctionType(ts.tail, ts.head)))
    case t => Some(Nil(), _ => t)
  }
}
  
