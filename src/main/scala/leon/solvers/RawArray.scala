package leon
package solvers

import purescala.Types._
import purescala.Expressions._

// Corresponds to a smt map, not a leon/scala array
private[solvers] case class RawArrayType(from: TypeTree, to: TypeTree) extends TypeTree

// Corresponds to a raw array value, which is coerced to a Leon expr depending on target type (set/array)
private[solvers] case class RawArrayValue(keyTpe: TypeTree, elems: Map[Expr, Expr], default: Expr) extends Expr {
  val getType = RawArrayType(keyTpe, default.getType)
}
