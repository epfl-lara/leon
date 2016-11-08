/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Definitions._
import purescala.Types._

import collection.mutable.{ Set => MutableSet }

private[genc] object ExtraOps {

  // Extra tools on FunDef, especially for annotations
  implicit class FunDefOps(val fd: FunDef) {
    def isMain = fd.id.name == "main"

    def isExtern          = hasAnnotation("extern")
    def isDropped         = hasAnnotation("cCode.drop")
    def isManuallyDefined = hasAnnotation(manualDefAnnotation)

    def getManualDefinition = {
      assert(isManuallyDefined)

      val Seq(Some(code0), includesOpt0) = fd.extAnnotations(manualDefAnnotation)
      val code      = code0.asInstanceOf[String]
      val includes0 = includesOpt0 map { _.asInstanceOf[String] } getOrElse ""

      val includes =
        if (includes0.isEmpty) Nil
        else { includes0 split ':' }.toSeq

      ManualDef(code.stripMargin, includes)
    }

    case class ManualDef(code: String, includes: Seq[String])

    def isGeneric = fd.tparams.length > 0

    private def hasAnnotation(annot: String) = fd.annotations contains annot
    private val manualDefAnnotation = "cCode.function"
  }

  // Extra tools on ClassDef, especially for annotations, inheritance & generics
  implicit class ClassDefOps(val cd: ClassDef) {
    def isManuallyTyped = hasAnnotation(manualTypeAnnotation)
    def isDropped       = hasAnnotation(droppedAnnotation)

    def getManualType = {
      assert(isManuallyTyped)

      val Seq(Some(alias0), includesOpt0) = cd.extAnnotations(manualTypeAnnotation)
      val alias   = alias0.asInstanceOf[String]
      val include = includesOpt0 map { _.asInstanceOf[String] } flatMap { i =>
        if (i.isEmpty) None else Some(i)
      }

      ManualType(alias, include)
    }

    case class ManualType(alias: String, include: Option[String])

    def isCandidateForInheritance = cd.isAbstract || cd.hasParent

    def isGeneric = cd.tparams.length > 0

    def isRecursive: Boolean = {
      val defs = (cd.parent map { _.classDef }).toSet + cd

      val seens = MutableSet[ClassType]()

      def rec(typ: TypeTree): Boolean = typ match {
        case t: ClassType if seens(t) => false

        case t: ClassType =>
          defs(t.classDef) || {
            seens += t

            (t.fields map { _.getType } exists rec) ||
            (t.parent exists rec) ||
            (t.knownCCDescendants exists rec)
          }

        case NAryType(ts, _) => ts exists rec

        case _ => false
      }

      // Find out if the parent of cd or cd itself are involved in a type of a field
      cd.fields map { _.getType } exists rec
    }

    // Check whether the class has some fields or not
    def isEmpty = cd.fields.isEmpty

    private def hasAnnotation(annot: String) = cd.annotations contains annot
    private val manualTypeAnnotation = "cCode.typedef"
    private val droppedAnnotation = "cCode.drop"
  }

  // Extra tools on ClassType, expecially for inheritance
  implicit class ClassTypeOps(val ct: ClassType) {
    def getTopParent: ClassType = ct.parent map { _.getTopParent } getOrElse { ct }
  }
}

