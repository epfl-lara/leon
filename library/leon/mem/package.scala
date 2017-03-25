/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import annotation._
import lang._
import collection._
import scala.language.implicitConversions
import scala.{sys,Any,Boolean}
import scala.Predef.ArrowAssoc

package object mem {

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
  def inSt[TAny]: Set[Fun[TAny]] = sys.error("inSt method is not executable!")

  @library
  @extern
  def outSt[TAny]: Set[Fun[TAny]] = sys.error("outSt method is not executable")

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
