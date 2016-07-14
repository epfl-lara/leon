package leon
package invariant.util

import purescala._
import Common._
import Expressions._
import ExprOps._
import Types._
import Definitions._
import invariant.factories._
import solvers._
import scala.collection.immutable._
import scala.collection.mutable.{ Set => MutableSet, Map => MutableMap }
import ExpressionTransformer._
import leon.evaluators._
import EvaluationResults._
import TypeUtil._

/**
 * This method changes the fields of the input class definition, based on the type map given
 * as input
 */
class ADTSpecializer {

  /**
   * This method copies the ADT hierarchy, but does not set the fields of the new hierarchy.
   * The fields should be set by calling `specializeFields`
   */
  def copyADTHierarchy(rootADT: ClassDef): Map[ClassDef, ClassDef] = rootADT match {
    case adef:  AbstractClassDef =>      
      val newAbs = new AbstractClassDef(FreshIdentifier(adef.id.name, Untyped, true), adef.tparams, adef.parent)
      ((adef -> newAbs) +: adef.knownCCDescendants.map { cc =>
        val parentType = cc.parent.map { case AbstractClassType(_, targs) => AbstractClassType(newAbs, targs) }
        val newCC = new CaseClassDef(FreshIdentifier(cc.id.name, Untyped, true), cc.tparams, parentType, cc.isCaseObject)
        newAbs.registerChild(newCC)
        cc -> newCC
      }).toMap
    case cdef: CaseClassDef if !cdef.parent.isDefined =>
      Map(cdef -> new CaseClassDef(FreshIdentifier(cdef.id.name, Untyped, true), cdef.tparams, None, cdef.isCaseObject))
  }

  /**
   * This method sets the fields of all case classes in the specialized ADT hierarchy (spelRoot)
   * using the specialization function passed as parameter.
   */
  def specializeFields(oldRoot: ClassDef, spelRoot: ClassDef, specializeFun: TypeTree => TypeTree) {
    def fieldReplacementMap(fields: Seq[ValDef]) = {
      var fldMap = Map[TypeTree, TypeTree]()
      fields.map(_.getType).foreach { t =>
        val rept = specializeFun(t)
        if (rept != t)
          fldMap += (t -> rept)
      }
      fldMap
    }
    val newTypeMap = oldRoot match {
      case absDef: AbstractClassDef =>
        absDef.typed.knownCCDescendants.flatMap { cc => fieldReplacementMap(cc.fields.toList) }.toMap
      case cdef: CaseClassDef =>
        fieldReplacementMap(cdef.fields.toList)
    }
    // replace every field type by the new type
    def translateFields(fields: List[ValDef], tparamMap: Map[TypeTree, TypeTree]): Seq[ValDef] = {
      fields map {
        case ValDef(id) =>
          val ntype = newTypeMap.find {
            case (oldt, newt) => id.getType == TypeOps.replace(tparamMap, oldt)
          }.map {
            case (_, newt) =>
              val rept = TypeOps.replace(tparamMap, newt)
              val capturedTparams = getTypeParameters(rept).toSet -- oldRoot.tparams.map(_.tp).toSet
              if (!capturedTparams.isEmpty) {
                //here, the new type has a type parameter that cannot be substituted by the type parameters of `absDef`
                throw new IllegalStateException(s"New type: $newt captures type parameters: $capturedTparams that do not belong to $oldRoot")
              } else rept
          }
          ValDef(FreshIdentifier(id.name, ntype.getOrElse(id.getType), true))
      }
    }
    (oldRoot, spelRoot) match {
      case (oldd: CaseClassDef, newd: CaseClassDef) if oldd.parent.isEmpty =>
        newd.setFields(translateFields(oldd.fields.toList, oldd.tparams.map(tpd => tpd.tp -> tpd.tp).toMap))
      case (oldd: AbstractClassDef, newd: AbstractClassDef) =>
        val children = (oldd.knownCCDescendants zip newd.knownCCDescendants) map {
          case (oldd, newd) =>
            val absToCCTparams: Map[TypeTree, TypeTree] = oldd.parent.get match {
              case AbstractClassType(_, targs) => (targs zip oldd.tparams.map(_.tp)).toMap
            }
            newd.setFields(translateFields(oldd.fields.toList, absToCCTparams))
        }
    }
  }

  //  var adtMap = Map[ClassDef, MutableMap[List[(TypeTree, TypeTree)], ClassDef]]() // a map from old adts to new adts
  //  def specializeFields(absDef: ClassDef, newTypeMap: Map[TypeTree, TypeTree]): ClassDef = {
  //    if (newTypeMap.isEmpty) absDef
  //    else {
  //      val adtSpels = adtMap.getOrElse(absDef, {
  //        val fresh = MutableMap[List[(TypeTree, TypeTree)], ClassDef]()
  //        adtMap += (absDef -> fresh)
  //        fresh
  //      })
  //      if (newTypeMap.isEmpty) absDef
  //      else {
  //        // replace every field type by the new type
  //        def translateFields(fields: List[ValDef], tparamMap: Map[TypeTree, TypeTree]): Seq[ValDef] = {
  //          fields map {
  //            case ValDef(id) =>
  //              val ntype = newTypeMap.find {
  //                case (oldt, newt) => id.getType == TypeOps.replace(tparamMap, oldt)
  //              }.map {
  //                case (_, newt) =>
  //                  val rept = TypeOps.replace(tparamMap, newt)
  //                  val capturedTparams = getTypeParameters(rept).toSet -- absDef.tparams.map(_.tp).toSet
  //                  if (!capturedTparams.isEmpty) {
  //                    //here, the new type has a type parameter that cannot be substituted by the type parameters of `absDef`
  //                    throw new IllegalStateException(s"New type: $newt captures type parameters: $capturedTparams that do not belong to $absDef")
  //                  } else rept
  //              }
  //              ValDef(FreshIdentifier(id.name, ntype.getOrElse(id.getType), true))
  //          }
  //        }
  //        val adef = adtSpels.get(newTypeMap.toList) match {
  //          case Some(nadt) => nadt
  //          case None =>
  //            absDef match {
  //              case ccd: CaseClassDef if ccd.parent.isEmpty =>
  //                val newCC = new CaseClassDef(FreshIdentifier(ccd.id.name, Untyped, true), ccd.tparams, None, ccd.isCaseObject)
  //                newCC.setFields(translateFields(ccd.fields.toList, ccd.tparams.map(tpd => tpd.tp -> tpd.tp).toMap))
  //                newCC
  //              case absDef: AbstractClassDef =>
  //                val newAbs = new AbstractClassDef(FreshIdentifier(absDef.id.name, Untyped, true), absDef.tparams, None)
  //                val children = absDef.knownCCDescendants map { cc =>
  //                  val absToCCTparams: Map[TypeTree, TypeTree] = cc.parent.get match {
  //                    case AbstractClassType(_, targs) => (targs zip absDef.tparams.map(_.tp)).toMap
  //                  }
  //                  val parentType = cc.parent.map { case AbstractClassType(_, targs) => AbstractClassType(newAbs, targs) }
  //                  val specialDef = new CaseClassDef(FreshIdentifier(cc.id.name, Untyped, true), cc.tparams, parentType, cc.isCaseObject)
  //                  specialDef.setFields(translateFields(cc.fields.toList, absToCCTparams))
  //                  newAbs.registerChild(specialDef)
  //                }
  //                newAbs
  //            }
  //        }
  //        adef
  //      }
  //    }
  //  }

  //  def fieldReplacementMap(spelOp: TypeTree => TypeTree)(fields: Seq[ValDef]) = {
  //    var fldMap = Seq[(TypeTree, TypeTree)]()
  //    fields.map(_.getType).foreach { t =>
  //      val instt = specializeType(spelOp)(t)
  //      if (t != instt)
  //        fldMap :+= (t, instt)
  //    }
  //    fldMap
  //  }
  //
  //  def specializeClassType(spelOp: TypeTree => TypeTree)(ct: ClassType): ClassType = ct match {
  //    case at: AbstractClassType =>
  //      val absDef = at.classDef
  //      val newTypeMap = absDef.typed.knownCCDescendants.flatMap { cc => fieldReplacementMap(spelOp)(cc.fields.toList) }.toMap
  //      AbstractClassType(specialize(absDef, newTypeMap).asInstanceOf[AbstractClassDef], at.tps)
  //
  //    case cct: CaseClassType if cct.parent.isDefined =>
  //      // transform the base class and chooses the descendant
  //      specializeClassType(spelOp)(cct.parent.get).knownCCDescendants.find(_.classDef.id.name == cct.classDef.id.name).get
  //
  //    case cct: CaseClassType =>
  //      CaseClassType(specialize(cct.classDef, fieldReplacementMap(spelOp)(cct.fields.toList).toMap).asInstanceOf[CaseClassDef], cct.tps)
  //  }
  //
  //  /**
  //   * SpelOp is an operation that matches a tree that needs to be modified and transforms it.
  //   * The function specializes the type by applying SpelOp transitively to all subtrees.
  //   * It is applied in preorder.
  //   */
  //  def specializeType(spelOp: TypeTree => TypeTree)(t: TypeTree): TypeTree = {
  //    spelOp(t) match {
  //      case ct: ClassType => specializeClassType(spelOp)(ct)
  //      case NAryType(tps, op) =>
  //        op(tps map specializeType(spelOp))
  //    }
  //  }
}