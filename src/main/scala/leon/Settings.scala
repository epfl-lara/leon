/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import utils.DebugSection

case class Settings(
  strictCompilation: Boolean       = true, // Terminates Leon in case an error occured during extraction
  terminateAfterEachPhase: Boolean = true, // Terminates Leon after each phase if an error occured
  debugSections: Set[DebugSection] = Set(), // Enables debug message for the following sections
  termination: Boolean             = false,
  repair: Boolean                  = false,
  synthesis: Boolean               = false,
  xlang: Boolean                   = false,
  verify: Boolean                  = true,
  selectedSolvers: Set[String]     = Set("fairz3")
)
