
package leon.theorem

import leon.collection.List

case class Identifier private (name: String)

sealed abstract class Term
case class Variable(name: Identifier) extends Term
case class Application(function: String, arguments: List[Term]) extends Term
case class Literal(value: String) extends Term

sealed abstract class Formula
case class And(left: Formula, right: Formula) extends Formula
case class Or(left: Formula, right: Formula) extends Formula
case class Implies(left: Formula, right: Formula) extends Formula
case class Iff(left: Formula, right: Formula) extends Formula
case class Not(formula: Formula) extends Formula
case class Forall(identifier: Identifier, formula: Identifier => Formula) extends Formula
case class Exists(identifier: Identifier, formula: Identifier => Formula) extends Formula
case class Equals(left: Term, right: Term) extends Formula
case object True extends Formula
case object False extends Formula

case class Theorem private (formula: Formula)