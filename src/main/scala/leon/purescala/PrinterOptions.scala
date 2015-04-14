/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import utils._

case class PrinterOptions (
  baseIndent: Int = 0,
  printPositions: Boolean = false,
  printTypes: Boolean = false,
  printUniqueIds: Boolean = false
)

object PrinterOptions {
  def fromContext(ctx: LeonContext): PrinterOptions = {
    val debugTrees     = ctx.settings.debugSections contains DebugSectionTrees
    val debugPositions = ctx.settings.debugSections contains DebugSectionPositions

    PrinterOptions(
      baseIndent     = 0,
      printPositions = debugPositions,
      printTypes     = debugTrees,
      printUniqueIds = debugTrees
    )
  }
}
