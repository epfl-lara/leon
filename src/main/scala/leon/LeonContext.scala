/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import purescala.Definitions.Program
import java.io.File

/** Everything that is part of a compilation unit, except the actual program tree.
 *  Contexts are immutable, and so should all there fields (with the possible
 *  exception of the reporter). */
case class LeonContext(
  settings: Settings = Settings(),
  options: Seq[LeonOption] = Seq(),
  files: Seq[File] = Seq(),
  reporter: Reporter = new DefaultReporter()
)
