package z3.scala
package dsl

import scala.annotation.implicitNotFound

/** A ValHandler encapsulates everything that is needed to build a Z3Sort
 * representing A, a fresh identifier of that sort and to reconstruct a Scala
 * value from a model. */
@implicitNotFound(msg = "The following type cannot be converted to Z3 : ${A}.")
abstract class ValHandler[A : Default] {
  // Note: it seems to be better at this point NOT to make ValHandler inherit
  // from Default. The reason is clarity while we're developing/refactoring.
  // From a logical/rational point of view, I believe it should in fact
  // inherit from Default and the implicit ValHandlers would serve as the
  // providers of default values. One argument against that is that Defaults
  // exist outside of the DSL while ValHandlers do not. PS.
  val default : Default[A] = implicitly[Default[A]]
  private val defaultValue : A = default.value

  /** Z3 code to construct a sort representing the Scala A type. */
  def mkSort(z3 : Z3Context) : Z3Sort

  /** Constructs a Val[A], i.e. the representation of a variable of type A. */
  def construct : Val[A] = new Val[A] {
    def build(z3 : Z3Context) = z3.mkFreshConst("valCst", mkSort(z3))
  }

  def convert(model : Z3Model, ast : Z3AST) : A
}
