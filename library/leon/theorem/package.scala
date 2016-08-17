
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

    def rename(from: Identifier, to: Identifier): Term = this match {
      case Variable(id) if (from == id) => Variable(to)
      case Let(binder, value, body) => {
        assert(binder != from && binder != to)

        Let(binder, value.rename(from, to), body.rename(from, to))
      }
      case Application(function, arguments) => 
        Application(function.rename(from, to), arguments.map(_.rename(from, to)))
      case FunctionInvocation(function, arguments) =>
        FunctionInvocation(function, arguments.map(_.rename(from, to)))
      case And(left, right) => And(left.rename(from, to), right.rename(from, to))
      case Or(left, right) => Or(left.rename(from, to), right.rename(from, to))
      case Implies(left, right) => Implies(left.rename(from, to), right.rename(from, to))
      case Iff(left, right) => Iff(left.rename(from, to), right.rename(from, to))
      case Not(formula) => Not(formula.rename(from, to))
      case Forall(binder, tpe, body) => {
        assert(binder != from && binder != to)

        Forall(binder, tpe, body.rename(from, to))
      }
      case Exists(binder, tpe, body) => {
        assert(binder != from && binder != to)

        Exists(binder, tpe, body.rename(from, to))
      }
      case Equals(left, right) => Equals(left.rename(from, to), right.rename(from, to))
      case BinOp(op, left, right) => BinOp(op, left.rename(from, to), right.rename(from, to))
      case UnOp(op, expr) => UnOp(op, expr.rename(from, to))
      case _ => this
    }
  }

  case class Type private (name: String)

  @library
  def getType[A](): Type = getType[A]()

  case class Variable(name: Identifier) extends Term
  case class Let(binder: Identifier, value: Term, body: Term) extends Term
  case class Application(function: Term, arguments: List[Term]) extends Term
  case class FunctionInvocation(function: String, arguments: List[Term]) extends Term
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
  case class Forall(binder: Identifier, tpe: Type, formula: Term) extends Term
  case class Exists(binder: Identifier, tpe: Type, formula: Term) extends Term
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
  case class Theorem private (formula: Term) {
    def &&(other: Theorem): Theorem = toTheorem(And(this.formula, other.formula))
    def ||(other: Theorem): Theorem = toTheorem(Or(this.formula, other.formula))
  }

  @library
  private def toTheorem(formula: Term): Theorem = toTheorem(formula)

  @library
  def fresh(name: String): Identifier = fresh(name)

  @library
  def prove(formula: Term): Theorem = toTheorem(formula)

  @library
  def contract(function: String): Theorem = contract(function)

  @library
  def modusPonens(pq: Theorem, r: Theorem): Theorem = pq.formula match {
    case Implies(p, q) if (p == r.formula) => toTheorem(q)
  }

  @library
  def instantiate(fa: Theorem, i: Identifier): Theorem = fa.formula match {
    case Forall(j, tpe, body) => toTheorem(body.rename(j, i))
  }

  @library
  def refl(term: Term): Theorem = toTheorem(Equals(term, term))

  @library
  val truth: Theorem = toTheorem(BooleanLiteral(true))

  @library
  def contradiction(term: Term, absurd: Theorem => Theorem): Theorem = {
    absurd(toTheorem(term)).formula match {
      case BooleanLiteral(false) => toTheorem(Not(term))
    }
  }

  @library
  def naturalInduction(formula: Identifier => Term, ground: Term, groundCase: Theorem, inductiveCase: Theorem => Theorem): Theorem = {

    // Base case.
    val z = fresh("z")
    prove(Implies(groundCase.formula, Let(z, ground, formula(z))))

    // Inductive case.
    val n = fresh("n")
    val hyp = toTheorem(And(formula(n), BinOp(">=", Variable(n), ground)))
    val succN = fresh("succN")
    prove(Implies(inductiveCase(hyp).formula, Let(succN, BinOp("+", Variable(n), 1), formula(succN))))

    val x = fresh("x")
    toTheorem(Forall(x, getType[BigInt], Implies(BinOp(">=", Variable(x), ground), formula(x))))
  }

  @library
  def hypothesis(term: Term, conclusion: Theorem => Theorem): Theorem = 
    toTheorem(Implies(term, conclusion(toTheorem(term)).formula))

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