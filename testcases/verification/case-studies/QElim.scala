import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

object QElim {
  case class Q(n: BigInt, d: BigInt) {
    assert(d > 0)
 
    def +(that: Q): Q = { Q(n*that.d + that.n*d, d*that.d) }
 
    def -(that: Q): Q = { Q(n*that.d - that.n*d, d*that.d) }
 
    def *(that: Q): Q = { Q(n*that.n, d*that.d) }
 
    def /(that: Q): Q = { Q(n*that.d, d*that.n) }
 
    // Equivalence of two rationals, true if they represent the same real number
    def ~(that: Q): Boolean = { n*that.d == that.n*d }

    def <(that: Q): Boolean = { (this - that).n < 0 }
    def <=(that: Q): Boolean = { (this - that).n <= 0 }
 
    def isRational = !(d == 0)
    def nonZero    = !(n == 0)
  }
  val zeroQ = Q(0,1)
  val oneQ = Q(1,1)

  sealed abstract class Formula
  case class Equal(lhs: Term, rhs: Term) extends Formula
  case class LessThan(lhs: Term, rhs: Term) extends Formula
  case class LessThanEq(lhs: Term, rhs: Term) extends Formula
  case class Not(f: Formula) extends Formula
  case class And(fs: List[Formula]) extends Formula
  case class Or(fs: List[Formula]) extends Formula

  sealed abstract class Term
  case class Var(id: BigInt) extends Term
  case class LinearCombination(kts: List[(Q,Term)]) extends Term
  case class IfThenElse(c: Formula, thn: Term, els: Term) extends Term
  case class Divide(t: Term, byConst: Q) extends Term

  case class Interp(m: Map[BigInt, Q])

  def evalF(f: Formula, alpha: Interp): Boolean = {
    f match {
      case Equal(lhs,rhs) => evalT(lhs,alpha) ~ evalT(rhs,alpha)
      case LessThan(lhs,rhs) => evalT(lhs,alpha) < evalT(rhs,alpha)
      case LessThanEq(lhs,rhs) => evalT(lhs,alpha) <= evalT(rhs,alpha)
      case Not(f) => !evalF(f,alpha)
      case And(fs) => fs.forall((f:Formula) => evalF(f,alpha))
      case Or(fs) => fs.exists((f:Formula) => evalF(f,alpha))
    }
  }
  def evalT(t: Term, alpha: Interp): Q = {
    t match {
      case Var(id) => alpha.m(id)
      case LinearCombination(kts) => {
        // This could not be extracted?
        // def addValue(q: Q, kt: (Q, Term)) = { q + kt._1 * evalT(kt._2,alpha) }
        kts.foldLeft(zeroQ)((q,kt) => q + kt._1 * evalT(kt._2,alpha))
      }
      case IfThenElse(c,thn,els) => {
        if (evalF(c,alpha)) evalT(thn,alpha) else evalT(els,alpha)
      }
      case Divide(t,c) => evalT(t,alpha) / c
    }
  }

  def onePoint(f: Formula, test: Q): Formula = {
    f
  }

}
