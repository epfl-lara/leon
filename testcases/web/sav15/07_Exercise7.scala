import leon.lang._

/**
 * 1) Implement operations on rationals: addition, substraction, multiplication and division
 *    Ensure that the results are rationals, add necessary preconditions.
 * 2) Implement rational equivalence (~).
 * 3) Write lemmas that show that if a1 ~ a2, and b1 ~ b2, then (a1 <op> b1) ~ (a2 <op> b2), for each <op>
 */
object Rationals {
  // Represents n/d
  case class Q(n: BigInt, d: BigInt) {

    def +(that: Q):Q = this // TODO

    def -(that: Q):Q = this // TODO

    def *(that: Q):Q = this // TODO

    def /(that: Q):Q = this // TODO

    // Equivalence of two rationals
    def ~(that: Q): Boolean = false // TODO

    def isRational = !(d == 0)
    def nonZero    = !(n == 0)
  }

  def lemma1(a1: Q, a2: Q, b1: Q, b2: Q): Boolean = {
    true // TODO
  }.holds
}

