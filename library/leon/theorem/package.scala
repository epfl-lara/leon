
package leon.theorem

import leon.collection.List

case class Identifier private (name: String)

sealed abstract class Term
case class Variable(name: Identifier) extends Term
case class Application(function: String, arguments: List[Term]) extends Term
case class BooleanLiteral(value: Boolean) extends Term
case class StringLiteral(value: String) extends Term
case class CharLiteral(value: Char) extends Term
case class IntLiteral(value: Int) extends Term
case class BigIntLiteral(value: BigInt) extends Term
case class And(left: Term, right: Term) extends Term
case class Or(left: Term, right: Term) extends Term
case class Implies(left: Term, right: Term) extends Term
case class Iff(left: Term, right: Term) extends Term
case class Not(formula: Term) extends Term
case class Forall(formula: Identifier => Term) extends Term
case class Exists(formula: Identifier => Term) extends Term
case class Equals(left: Term, right: Term) extends Term

case class Theorem private (formula: Term)