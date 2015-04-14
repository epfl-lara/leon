/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import leon.utils._

import java.io.File

/** Everything that is part of a compilation unit, except the actual program tree.
 *  Contexts are immutable, and so should all there fields (with the possible
 *  exception of the reporter). */
case class LeonContext(
  reporter: Reporter,
  interruptManager: InterruptManager,
  settings: Settings = Settings(),
  options: Seq[LeonOption] = Seq(),
  files: Seq[File] = Seq(),
  timers: TimerStorage = new TimerStorage
)
