import leon.lang._
import leon.lang.synthesis._
import leon.collection._
import leon.annotation._

object Running {
  abstract class Formula
  case class And(a: Formula, b: Formula) extends Formula
  case class Or (a: Formula, b: Formula) extends Formula
  case class Implies(a: Formula, b: Formula) extends Formula
  case class Not(a: Formula) extends Formula
  case object LitFalse extends Formula
  case object LitTrue extends Formula

  def desugar(f: Formula): Formula = {
    f match {
      case And(a, b) =>
        And(desugar(a), desugar(b))
      case Or(a, b) =>
        Or(desugar(a), desugar(b))
      case Implies(a, b) =>
        if (a == LitFalse) {
          LitTrue
        } else {
          Or(Not(a), b)
        }
      case Not(Not(a)) =>
        desugar(a)
      case Not(a) =>
        Not(desugar(a))
      case f =>
        f
    }
  } ensuring {
    res => !existsImplies(res) && eval(res) == eval(f)
  }

  def existsImplies(f: Formula): Boolean = f match {
    case Implies(a, b) => true
    case And(a, b)     => existsImplies(a) || existsImplies(b)
    case Or(a, b)      => existsImplies(a) || existsImplies(b)
    case Not(a)        => existsImplies(a)
    case _             => false
  }

  def eval(f: Formula): Boolean = f match {
    case Implies(a, b) => !eval(a) || eval(b)
    case And(a, b)     => eval(a) && eval(b)
    case Or(a, b)      => eval(a) || eval(b)
    case Not(a)        => !eval(a)
    case LitFalse      => false
    case LitTrue       => true
  }
  
}
