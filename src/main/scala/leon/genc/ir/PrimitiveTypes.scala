/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package ir

/*
 * Collection of the primitive types for IR.
 */
private[genc] object PrimitiveTypes {

  sealed abstract class PrimitiveType {
    def isLogical: Boolean = this match {
      case BoolType => true
      case _ => false
    }

    def isIntegral: Boolean = this match {
      case CharType | Int32Type => true
      case _ => false
    }
  }

  case object CharType extends PrimitiveType
  case object Int32Type extends PrimitiveType
  case object BoolType extends PrimitiveType
  case object UnitType extends PrimitiveType
  case object StringType extends PrimitiveType

}

