package cp

import Serialization._
import purescala.Trees._

object Trees {
  final class NotImplementedException extends Exception

  abstract class Constraint1[A] {
    def ||(other: Constraint1[A]): Constraint1[A] = OrConstraint1[A](this, other)

  }

  case class BaseConstraint1[A](serializedInputVars : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr])

  object OrConstraint1 {
    def apply[A](l: Constraint1[A], r: Constraint1[A]): Constraint1[A] = {
      new OrConstraint1[A](Seq(l,r))
    }
  }

  class OrConstraint1[A](exprs: Seq[Constraint1[A]]) extends Constraint1[A]
}
