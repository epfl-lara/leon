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
  case class Fun[T](v: T) {
    @extern
    def cached: Boolean = sys.error("not implemented!")
  }

  @library
  @inline
  implicit def toMem[T](x: T) = new Fun(x)

  /**
   * accessing in and out states. Should be used only in ensuring.
   * The type can be anything that will let the program type check in Leon.
   */
  @library
  @extern
  def inState[Any]: Set[Fun[Any]] = sys.error("inState method is not executable!")

  @library
  @extern
  def outState[Any]: Set[Fun[Any]] = sys.error("outState method is not executable")

  /**
   * Helper class for invoking with a given state instead of the implicit state
   */
  @library
  case class memWithState[T](v: T) {
    @extern
    def withState[U](u: Set[Fun[U]]): T = sys.error("withState method is not executable!")
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
  case class Star[T](f: T) {
    def * = f
  }
  
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
  def lookup[T](args:List[Any]): (Boolean, T) = {
    if(memoTable.contains(args)) {
      (true, memoTable(args).asInstanceOf[T])      
    } else {
      (false, null.asInstanceOf[T]) // for ints and bools this will be zero, false
    }
  }
  @ignore
  def clearMemo()  = {
    memoTable = Map[List[Any], Any]() 
  }    
}