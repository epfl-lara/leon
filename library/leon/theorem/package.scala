
package leon

import leon.collection.List

package object theorem {

  case class Identifier private (name: String)

  sealed abstract class Term
  case class Variable(name: Identifier) extends Term
  case class Let(binder: Identifier, value: Term, body: Term) extends Term
  case class Application(function: Term, arguments: List[Term]) extends Term
  case class FunctionInvocation(function: String, arguments: List[Term]) extends Term
  case class MethodInvocation(obj: Term, clss: String, arguments: List[Term]) extends Term
  case class BooleanLiteral(value: Boolean) extends Term
  case class StringLiteral(value: String) extends Term
  case class CharLiteral(value: Char) extends Term
  case class IntLiteral(value: Int) extends Term
  case class BigIntLiteral(value: BigInt) extends Term
  case class UnitLiteral() extends Term
  case class And(left: Term, right: Term) extends Term
  case class Or(left: Term, right: Term) extends Term
  case class Implies(left: Term, right: Term) extends Term
  case class Iff(left: Term, right: Term) extends Term
  case class Not(formula: Term) extends Term
  case class Forall(formula: Identifier => Term) extends Term
  case class Exists(formula: Identifier => Term) extends Term
  case class Equals(left: Term, right: Term) extends Term
  case class BinOp(name: String, left: Term, right: Term) extends Term
  case class UnOp(name: String, expr: Term) extends Term

  case class Theorem(formula: Term)

  private def toTheorem(formula: Term): Theorem = Theorem(formula)

  def prove(formula: Term): Theorem = toTheorem(formula)
}