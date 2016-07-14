/* Copyright 2009-2016 EPFL, Lausanne */

/** Core package of the Leon system 
  *
  * Provides the basic types and definitions for the Leon system.
  */
package object leon {
  implicit class BooleanToOption(cond: Boolean) {
    def option[A](v: => A) = if (cond) Some(v) else None
  }
}
