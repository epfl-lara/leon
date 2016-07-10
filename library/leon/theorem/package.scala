
package leon

import leon.annotation._
import leon.collection._
import leon.lang._

package object theorem {

  case class Identifier private (name: String)

  @library
  sealed abstract class Term {
    def +(other: Term) = BinOp("+", this, other)
    def -(other: Term) = BinOp("-", this, other)

    def ==>(other: Term) = Implies(this, other)
    def &&(other: Term) = And(this, other)
    def ||(other: Term) = Or(this, other)

    def by(proof: Theorem): Step = Step(this, proof)
  }

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
  case class Forall(binder: Identifier, tpe: String, formula: Term) extends Term
  case class Exists(binder: Identifier, tpe: String, formula: Term) extends Term
  case class Equals(left: Term, right: Term) extends Term
  case class BinOp(name: String, left: Term, right: Term) extends Term
  case class UnOp(name: String, expr: Term) extends Term

  // Implicit convertions
  implicit def booleanLiteral(value: Boolean): Term = BooleanLiteral(value)
  implicit def bigIntLiteral(value: BigInt): Term = BigIntLiteral(value)
  implicit def intLiteral(value: Int): Term = IntLiteral(value)
  implicit def stringLiteral(value: String): Term = StringLiteral(value)
  implicit def charLiteral(value: Char): Term = CharLiteral(value)
  implicit def unitLiteral(value: Unit): Term = UnitLiteral()

  @library
  case class Theorem(formula: Term) {
    def &&(other: Theorem): Theorem = Theorem(And(this.formula, other.formula))
    def ||(other: Theorem): Theorem = Theorem(Or(this.formula, other.formula))
  }

  private def toTheorem(formula: Term): Theorem = Theorem(formula)

  @library
  def fresh(name: String): Identifier = fresh(name)

  @library
  def prove(formula: Term): Theorem = toTheorem(formula)

  @library
  def modusPonens(pq: Theorem, r: Theorem): Option[Theorem] = pq.formula match {
    case Implies(p, q) if (p == r.formula) => Some(toTheorem(q))
    case _ => None()
  }

  @library
  def refl(term: Term): Theorem = toTheorem(Equals(term, term))

  @library
  val truth: Theorem = toTheorem(BooleanLiteral(true))

  @library
  def contradiction(term: Term, absurd: Theorem => Theorem): Option[Theorem] = {
    absurd(toTheorem(term)).formula match {
      case BooleanLiteral(false) => Some(toTheorem(Not(term)))
      case _ => None()
    }
  }

  @library
  private def go(current: Term, steps: List[Step]): Term = steps match {
    case Nil() => current
    case Cons(Step(next, proof), rest) => {
      prove(proof.formula ==> Equals(current, next))
      go(next, rest)
    }
  }

  @library
  def chainEquals(first: Term, steps: List[Step]): Theorem = {

    toTheorem(Equals(first, go(first, steps)))
  }

  case class Step(term: Term, proof: Theorem)
}