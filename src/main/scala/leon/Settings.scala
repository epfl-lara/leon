/* Copyright 2009-2014 EPFL, Lausanne */

package leon

import utils.DebugSection

case class Settings(
  val strictCompilation: Boolean       = true, // Terminates Leon in case an error occured during extraction
  val terminateAfterEachPhase: Boolean = true, // Terminates Leon after each phase if an error occured
  val debugSections: Set[DebugSection] = Set(), // Enables debug message for the following sections
  val termination: Boolean             = false,
  val repair: Boolean                  = false,
  val synthesis: Boolean               = false,
  val xlang: Boolean                   = false,
  val verify: Boolean                  = true,
  val selectedSolvers: Set[String]     = Set("fairz3")
)
