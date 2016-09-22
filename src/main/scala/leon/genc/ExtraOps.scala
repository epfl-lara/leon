/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Definitions._
import purescala.Types._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

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

      ManualDef(code, includes)
    }

    case class ManualDef(code: String, includes: Seq[String])

    private def hasAnnotation(annot: String) = fd.annotations contains annot
    private val manualDefAnnotation = "cCode.function"
  }

  // Extra tools on ClassDef, especially for annotations
  implicit class ClassDefOps(val cd: ClassDef) {
    def isManuallyTyped = hasAnnotation(manualTypeAnnotation)
    def isDropped       = hasAnnotation(droppedAnnotation)

    def getManualType = {
      assert(isManuallyTyped)

      val Seq(Some(alias0), includesOpt0) = cd.extAnnotations(manualTypeAnnotation)
      val alias   = alias0.asInstanceOf[String]
      val include = includesOpt0 map { _.asInstanceOf[String] } getOrElse ""

      ManualType(alias, include)
    }

    case class ManualType(alias: String, include: String)

    def getTopParent: ClassDef = {
      cd.parent map { case AbstractClassType(acd, _) => acd.getTopParent } getOrElse { cd }
    }

    def isCandidateForInheritance = cd.isAbstract || cd.hasParent

    private def hasAnnotation(annot: String) = cd.annotations contains annot
    private val manualTypeAnnotation = "cCode.typedef"
    private val droppedAnnotation = "cCode.drop"
  }
}

