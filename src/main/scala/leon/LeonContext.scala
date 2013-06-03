/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import purescala.Definitions.Program
import java.io.File

/** Everything that is part of a compilation unit, except the actual program tree.
 *  Contexts are immutable, and so should all there fields (with the possible
 *  exception of the reporter). */
case class LeonContext(
  val settings: Settings          = Settings(),
  val options: Seq[LeonOption]    = Seq.empty,
  val files: Seq[File]            = Seq.empty,
  val reporter: Reporter          = new DefaultReporter
)
