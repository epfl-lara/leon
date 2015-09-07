/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import purescala.Types._
import purescala.Expressions._

// Corresponds to a complete map (SMT Array), not a Leon/Scala array
// Only used within solvers or SMT for encoding purposes
case class RawArrayType(from: TypeTree, to: TypeTree) extends TypeTree {
  override def asString(implicit ctx: LeonContext) = {
    s"RawArrayType[${from.asString}, ${to.asString}]"
  }
}

// Corresponds to a raw array value, which is coerced to a Leon expr depending on target type (set/array)
case class RawArrayValue(keyTpe: TypeTree, elems: Map[Expr, Expr], default: Expr) extends Expr {
  val getType = RawArrayType(keyTpe, default.getType)

  override def asString(implicit ctx: LeonContext) = {
    val elemsString = elems.map { case (k, v) => k.asString+" -> "+v.asString } mkString(", ")
    s"RawArray[${keyTpe.asString}]($elemsString, default = ${default.asString})"
  }
}
