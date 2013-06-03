/* Copyright 2009-2013 EPFL, Lausanne */

package leon

/** A common trait for everything that is important enough to be named,
 *  and that processes command line options. And important category are
 *  `LeonPhase`s. */
trait LeonComponent {
  val name : String
  val description : String

  val definedOptions : Set[LeonOptionDef] = Set()
}
