/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Types._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

import utils.Position

import ExtraOps._

private[genc] trait TypeAnalyser {
  this: CConverter =>

  // TODO This might need to be generalised...
  //  - One problem is with typedefs: should the type be returnable or not? The user might
  //    need to specify it manually.
  //  - Another issue is with case class with mutable members; references will get broken
  //    (not supported at all ATM).
  def containsArrayType(typ: TypeTree)(implicit pos: Position): Boolean = typ match {
    case CharType             => false
    case Int32Type            => false
    case BooleanType          => false
    case UnitType             => false
    case StringType           => false // NOTE this might change in the future
    case IntegerType          => CAST.unsupported(s"BigInt")
    case ArrayType(_)         => true
    case TupleType(bases)     => bases exists containsArrayType

    case CaseClassType(cd, _) =>
      if (cd.isDropped)
        CAST.unsupported(s"Using a dropped type")

      // If a case class is manually typdef'd, consider it to be a "returnable" type
      if (getTypedef(cd).isDefined) false
      else cd.fields map { _.getType } exists containsArrayType

    case _: AbstractClassType => CAST.unsupported(s"abstract classes $typ")
    case _                    => CAST.unsupported(s"Unexpected TypeTree '$typ': ${typ.getClass}")
  }

}

