/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import annotation._
import lang._
import collection._
import scala.language.implicitConversions
import scala.annotation.StaticAnnotation

package object mem {

  /**
   * A class representing named function calls. These are entities that are memoized.
   * This should be applied only over a function invocation or lambda application.
   */
  @library
  @isabelle.typ(name = "Leon_Types.fun")
  @isabelle.constructor(name = "Leon_Types.fun.Fun")
  case class Fun[T](v: T)

  @library
  @extern
  def cached[T](v: Fun[T]): Boolean = {
    sys.error("not implemented!")
  }

  /*@library
  @extern
  def cached[T](f: Fun[T]): Boolean = sys.error("not implemented!")*/

  @library
  @inline
  implicit def toMem[T](x: T) = new Fun(x)

  /**
   * accessing in and out states. Should be used only in ensuring.
   * The type can be anything that will let the program type check in Leon.
   */
  @library
  @extern
  def inSt[Any]: Set[Fun[Any]] = sys.error("inSt method is not executable!")

  @library
  @extern
  def outSt[Any]: Set[Fun[Any]] = sys.error("outSt method is not executable")

  /**
   * Helper class for invoking with a given state instead of the implicit state
   */
  @library
  @isabelle.typ(name = "Leon_Types.mem_with_state")
  @isabelle.constructor(name = "Leon_Types.mem_with_state.Mem_With_State")
  case class memWithState[T](v: T) {
    @extern
    def in[U](u: Set[Fun[U]]): T = sys.error("in method is not executable!")
  }

  @library
  @inline
  implicit def toWithState[T](x: T) = new memWithState(x)

  /**
   * A unary operator that should be applied over lambda Application or function invocation
   * if one is not interested in the time taken by the call but only in the value of the call.
   */
  @library
  @inline
  implicit def toStar[T](f: T) = new Star(f)

  @library
  @isabelle.typ(name = "Leon_Types.star")
  @isabelle.constructor(name = "Leon_Types.star.Star")
  case class Star[T](f: T) {
    def * = f
  }

  /**
   * A predicate that returns true if the input (direct or indirect) argument preserves state.
   * The argument should be of a function type. Each possible target of the call should then
   * be annotated invstate
   */
  @library
  @extern
  def invstateFun[T](f: T): Boolean = sys.error("invStateFun method is not executable!")

  /**
   * methods for running instrumented code using memoization
   */
  @ignore
  var memoTable = Map[List[Any], Any]()
  @ignore
  def update[T](args: List[Any], res: T): T = {
    memoTable += (args -> res)
    res
  }
  @ignore
  def lookup[T](args: List[Any]): (Boolean, T) = {
    if (memoTable.contains(args)) {
      (true, memoTable(args).asInstanceOf[T])
    } else {
      (false, null.asInstanceOf[T]) // for ints and bools this will be zero, false
    }
  }
}
