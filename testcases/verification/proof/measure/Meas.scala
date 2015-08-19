/* Copyright 2009-2015 EPFL, Lausanne */

package leon.testcases.verification.proof.measure

import leon.annotation._
import leon.collection._
import leon.lang._
import leon.proof._

/**
 * Measures on discrete probability spaces.
 *
 * NOTE:
 *
 * This class is a rather limited model of (discrete) measures in
 * that weights can only be rationals.  However, attention has been
 * payed to not rely on the properties of rationals, so that, in
 * principle, the class could be re-implemented using 'Real' instead
 * of 'Rational'.
 */
sealed abstract class Meas[A] {

  /** Compute the value of this measure on the space 'A'. */
  def apply(): Rational = {
    require(this.isMeasure)
    this match {
      case Empty()       => Rational(0, 1)
      case Cons(x, w, m) => w + m()
    }
  } ensuring { res =>
    res.isPositive because {
      this match {
        case Empty()       => trivial
        case Cons(x, w, m) => m().isPositive
      }
    }
  }

  /** Compute the value of this measure on a subset of the space 'A'. */
  def apply(xs: Set[A]): Rational = {
    require (isMeasure)
    this match {
      case Empty()       => Rational(0, 1)
      case Cons(x, w, m) => if (xs contains x) w + m(xs) else m(xs)
    }
  } ensuring { res =>
    res.isPositive because {
      this match {
        case Empty()       => trivial
        case Cons(x, w, m) => m(xs).isPositive
      }
    }
  }

  /** Compute the support of this measure. */
  def support: Set[A] = {
    require (isMeasure)
    this match {
      case Empty()       => Set()
      case Cons(x, w, m) =>
        if (w > BigInt(0)) m.support ++ Set(x) else m.support
    }
  }

  /** Restrict the measure to a subset of 'A'. */
  def filter(p: A => Boolean): Meas[A] = {
    require (isMeasure)
    this match {
      case Empty()       => Empty[A]()
      case Cons(x, w, m) => if (p(x)) Cons(x, w, m filter p) else m filter p
    }
  } ensuring (_.isMeasure)

  /** Change the space underlying this measure. */
  def map[B](f: A => B): Meas[B] = {
    require (isMeasure)
    this match {
      case Empty()       => Empty[B]()
      case Cons(x, w, m) => Cons(f(x), w, m map f)
    }
  } ensuring (_.isMeasure)

  /** Scalar multiplication. */
  def *(a: Rational): Meas[A] = {
    require(a.isRational && a.isPositive && isMeasure)
    this match {
      case Empty()       => Empty[A]()
      case Cons(x, w, m) => Cons(x, w * a, m * a)
    }
  } ensuring (_.isMeasure)

  /** Union/sum. */
  def +(that: Meas[A]): Meas[A] = {
    require (this.isMeasure && that.isMeasure)
    this match {
      case Empty()       => that
      case Cons(x, w, m) => Cons(x, w, m + that)
    }
  } ensuring (_.isMeasure)

  /** Compute the product of this measure and 'that'. */
  def *[B](that: Meas[B]): Meas[(A, B)] = {
    require (this.isMeasure && that.isMeasure)
    this match {
      case Empty()       => Empty[(A, B)]()
      case Cons(x, w, m) => (that map { y: B => (x, y) }) * w + m * that
    }
  } ensuring (_.isMeasure)

  /** Independence of two events in 'A'. */
  def indep(xs: Set[A], ys: Set[A]): Boolean = {
    require (this.isMeasure)
    this(xs ++ ys) ~ (this(xs) * this(ys))
  }

  /** Check if this measure is a probability. */
  def isProb: Boolean = isMeasure && this() ~ BigInt(1)

  /*

   TODO: the following need additional lemmas to be verified.

  /**
   * Compute the expected value/integral of a function 'f' with
   * respect to this measure.
   */
  def expect(f: A => Rational): Rational = {
    require(this.isMeasure &&
      setForall(this.support, { x: A => f(x).isRational }))
    this match {
      case Empty()       => BigInt(0)
      case Cons(x, w, m) => f(x) * w + m.expect(f)
    }
  }

  /** Convert this measure into a map. */
  def toMap: Map[A, Rational] = {
    this match {
      case Empty()       => Map()
      case Cons(x, w, m) => {
        val res: Map[A, Rational] = m.toMap
        val y = if (res isDefinedAt x) res(x) + w else w
        res.updated(x, y)
      }
    }
  } ensuring { res =>
    val sup = this.support
    setForall(sup, { x: A => (sup contains x) ==> (res isDefinedAt x) })
  }

   */

  /** All weights must be positive. */
  def isMeasure: Boolean = this match {
    case Empty()       => true
    case Cons(x, w, m) => w.isPositive && m.isMeasure
  }
}

/** The empty measure maps every subset of the space A to 0. */
case class Empty[A]() extends Meas[A]

/**
 * The 'Cons' measure adjoins an additional element 'x' of type 'A'
 * to an existing measure 'm' over 'A'.  Note that 'x' might already
 * be present in 'm'.
 */
case class Cons[A](x: A, w: Rational, m: Meas[A]) extends Meas[A]

import RationalSpecs._

object MeasSpecs {

  def additivity[A](m: Meas[A], xs: Set[A], ys: Set[A]): Boolean = {
    require(m.isMeasure && (xs & ys).isEmpty)
    m(xs ++ ys) == m(xs) + m(ys) because {
      m match {
        case Empty()       => trivial
        case Cons(x, w, n) => if (xs contains x) {
          w + n(xs ++ ys)     ==| additivity(n, xs, ys)        |
          w + (n(xs) + n(ys)) ==| plusAssoc(w, n(xs), n(ys))   |
          (w + n(xs)) + n(ys) ==| !(ys contains x)             |
          m(xs)       + m(ys)
        }.qed else if (ys contains x) {
          w + n(xs ++ ys)     ==| additivity(n, xs, ys)        |
          w + (n(xs) + n(ys)) ==| plusComm(w, (n(xs) + n(ys))) |
          (n(xs) + n(ys)) + w ==| plusAssoc(n(xs), n(ys), w)   |
          n(xs) + (n(ys) + w) ==| plusComm(n(ys), w)           |
          n(xs) + (w + n(ys)) ==| !(xs contains x)             |
          m(xs) + m(ys)
        }.qed else {
          n(xs ++ ys)         ==| additivity(n, xs, ys)        |
          n(xs) + n(ys)
        }.qed
      }
    }
  }.holds

  /**
   * Subaddititivity of measures.
   *
   * NOTE: the proof of this lemma could greatly benefit from a DSL
   * for relational reasoning on rationals.  However, the out-of-the-
   * box support for relational reasoning doesn't work here because
   *
   *  a) relations such as '<=' and '~' on rationals have
   *     preconditions that seem to interact badly with the generic
   *     relational reasoning DSL, and
   *
   *  b) although relations such as '<=' and '~' are transitive, this
   *     fact isn't obvious to Leon.  Consequently, one needs to
   *     establish that the composition of e.g. two '<='-reasoning
   *     steps is again in '<=' explicitly by calls to
   *     'orderingTransitivity' and the like.
   */
  def subAdditivity[A](m: Meas[A], xs: Set[A], ys: Set[A]): Boolean = {
    require(m.isMeasure)
    m(xs ++ ys) <= m(xs) + m(ys) because {
      m match {
        case Empty()       => trivial
        case Cons(x, w, n) => if (xs contains x) check {
          w + n(xs ++ ys) <= w + (n(xs) + n(ys)) because
            subAdditivity(n, xs, ys) &&
            additionPreservesOrdering(n(xs ++ ys), n(xs) + n(ys), w)
        } && check {
          if (ys contains x) check {
            w + (n(xs) + n(ys)) <= w + (n(xs) + n(ys)) + w because
              w + (n(xs) + n(ys)) == w + (n(xs) + n(ys)) + BigInt(0) &&
              additionPreservesOrdering(BigInt(0), w, w + (n(xs) + n(ys)))
          } && check {
            w + n(xs ++ ys) <= w + (n(xs) + n(ys)) + w because
              orderingTransitivity(
                w + n(xs ++ ys),
                w + (n(xs) + n(ys)),
                w + (n(xs) + n(ys)) + w)
          } && {
            w + (n(xs) + n(ys)) + w   ==| plusAssoc(w, n(xs), n(ys))     |
            (w + n(xs)) + n(ys) + w   ==| plusAssoc(w + n(xs), n(ys), w) |
            (w + n(xs)) + (n(ys) + w) ==| trivial                        |
            m(xs)       + m(ys)
          }.qed else {
            w + (n(xs) + n(ys))       ==| plusAssoc(w, n(xs), n(ys))   |
            (w + n(xs)) + n(ys)       ==| !(ys contains x)             |
            m(xs)       + m(ys)
          }.qed
        } else {
          if (ys contains x) check {
            w + n(xs ++ ys) <= w + (n(xs) + n(ys)) because
              subAdditivity(n, xs, ys) &&
              additionPreservesOrdering(n(xs ++ ys), n(xs) + n(ys), w)
          } && {
            w + (n(xs) + n(ys))       ==| plusComm(w, (n(xs) + n(ys))) |
            (n(xs) + n(ys)) + w       ==| plusAssoc(n(xs), n(ys), w)   |
            n(xs) + (n(ys) + w)       ==| plusComm(n(ys), w)           |
            n(xs) + (w + n(ys))       ==| !(xs contains x)             |
            m(xs) + m(ys)
          }.qed else {
            n(xs ++ ys) <= n(xs) + n(ys) because subAdditivity(n, xs, ys)
          }
        }
      }
    }
  }.holds
}
