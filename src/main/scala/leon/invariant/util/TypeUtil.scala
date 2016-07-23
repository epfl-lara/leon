package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._

object TypeUtil {
  def getTypeParameters(t: TypeTree): Seq[TypeParameter] = {
    t match {
      case tp @ TypeParameter(_) => Seq(tp)
      case NAryType(tps, _) =>
        (tps flatMap getTypeParameters).distinct
    }
  }

  /**
   * Computes the type arguments of `argt` w.r.t that of `t`
   */
  def getTypeArguments(argt: TypeTree, reft: TypeTree): Option[Seq[TypeTree]] = {
    typeInstMap(argt, reft) match {
      case Some(tmap) =>
        Some(getTypeParameters(reft).map(tmap.apply))
      case _ => None
    }
  }

  def isSubclass(sub: ClassDef, sup: ClassDef) = {
    sub == sup || (sub.parent.isDefined && sub.parent.get.classDef == sup)
  }

  def typeInstMap(argt: TypeTree, reft: TypeTree): Option[Map[TypeParameter, TypeTree]] = {
    var instMap = Map[TypeParameter, TypeTree]()
    def addMapping(tp: TypeParameter, targ: TypeTree) = {
      if (instMap.contains(tp)) instMap(tp) == targ
      else {
        instMap += (tp -> targ)
        true
      }
    }
    def rec(t1: TypeTree, t2: TypeTree): Boolean =
      (t1, t2) match {
        case (t1: ClassType, t2: ClassType) =>
          if (isSubclass(t1.classDef, t2.classDef))
            (t1.tps zip t2.tps).forall { case (x, y) => rec(x, y) }
          else false
        case (targ, tp: TypeParameter) => addMapping(tp, targ)
        case (_: TypeParameter, _)     => false // here, the right type is not a type parameter
        case (NAryType(tps1, _), NAryType(tps2, _)) =>
          tps1.size == tps2.size && (tps1 zip tps2).forall { case (x, y) => rec(x, y) }
      }
    if (rec(argt, reft)) {
      Some(instMap)
    } else None
  }

  /**
   * Uses a canonical naming for type parameters
   */
  def canonTypeName(it: TypeTree): String = {
    val tparamsIndex = getTypeParameters(it).zipWithIndex.toMap // gets type parameters in a particular order
    def rec(t: TypeTree): String = t match {
      case ct: ClassType         => ct.id.name + ct.tps.map(rec).mkString("")
      case TupleType(ts)         => "Tup" + ts.map(rec).mkString("")
      case ArrayType(t)          => "Array" + rec(t)
      case SetType(t)            => "Set" + rec(t)
      case MapType(from, to)     => "Map" + rec(from) + "t" + rec(to)
      case FunctionType(fts, tt) => fts.map(rec).mkString("x") + "t" + rec(tt)
      case t: TypeParameter      => "T" + tparamsIndex(t)
      case prim                  => prim.toString
    }
    rec(it)
  }

  /**
   * Checks if one type can be got by instantiating the other.
   * Slightly over-approximates this by ignoring the correlation between the type parameters,
   * and relationship between classes. Eg. Conc[Int] is an instance of Abs[T], but Conc[T] is
   * not an instance of Abs[Int].
   */
  def isTypeInstance(t1: TypeTree, t2: TypeTree): Boolean = {
    (t1, t2) match {
      case (t1: ClassType, t2: ClassType) =>
        (isSubclass(t1.classDef, t2.classDef) || isSubclass(t2.classDef, t1.classDef)) &&
          (t1.tps zip t2.tps).forall { case (x, y) => isTypeInstance(x, y) }
      case (_: TypeParameter, _) => true
      case (_, _: TypeParameter) => true
      case (NAryType(Seq(), _), NAryType(Seq(), _)) => // represents primitive types
        t1 == t2
      case (NAryType(tps1, _), NAryType(tps2, _)) =>
        tps1.size == tps2.size && (tps1 zip tps2).forall { case (x, y) => isTypeInstance(x, y) }
    }
  }
  
  /**
   * A helper class that uses isTypeInstance as equality
   */
  class CompatibleType(val baset: TypeTree) {
    override def equals(other: Any) = other match {
      case ot : CompatibleType => 
        isTypeInstance(baset, ot.baset)        
      case _ => false
    }   
    val hcode = baset match {
      case NAryType(tps, _) => tps.size      
    }
    override def hashCode = hcode
    override def toString = baset.toString()
  }

  def typeNameWOParams(t: TypeTree): String = t match {
    case ct: ClassType     => ct.id.name
    case TupleType(ts)     => ts.map(typeNameWOParams).mkString("(", ",", ")")
    case ArrayType(t)      => s"Array[${typeNameWOParams(t)}]"
    case SetType(t)        => s"Set[${typeNameWOParams(t)}]"
    case MapType(from, to) => s"Map[${typeNameWOParams(from)}, ${typeNameWOParams(to)}]"
    case FunctionType(fts, tt) =>
      val ftstr = fts.map(typeNameWOParams).mkString("-")
      ftstr + "To" + typeNameWOParams(tt)
    case t => t.toString
  }

  def instantiateTypeParameters(tpMap: Map[TypeParameter, TypeTree])(t: TypeTree): TypeTree = {
    t match {
      case tp: TypeParameter => tpMap.getOrElse(tp, tp)
      case NAryType(subtypes, tcons) =>
        tcons(subtypes map instantiateTypeParameters(tpMap) _)
    }
  }

  def isNumericType(t: TypeTree) = t match {
    case IntegerType | RealType => true
    case Int32Type =>
      throw new IllegalStateException("BitVector types not supported yet!")
    case _ => false
  }

  def rootType(t: TypeTree): Option[AbstractClassType] = t match {
    case absT: AbstractClassType => Some(absT)
    case ct: CaseClassType       => ct.parent
    case _                       => None
  }

  def uninstantiatedType(tp: TypeTree): TypeTree = tp match {
    case CaseClassType(ccd, tps) => ccd.typed
    case FunctionType(argts, rett) =>
      FunctionType(argts.map(uninstantiatedType), uninstantiatedType(rett))
    case NAryType(tps, op) =>
      op(tps.map(uninstantiatedType))
  }
}