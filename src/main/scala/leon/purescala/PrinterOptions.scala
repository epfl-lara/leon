/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import utils._

case class PrinterOptions (
  baseIndent: Int = 0,
  printPositions: Boolean = false,
  printUniqueIds: Boolean = false,
  printTypes: Boolean = false
)

object PrinterOptions {
  def fromContext(ctx: LeonContext): PrinterOptions = {
    val debugTrees     = ctx.findOptionOrDefault(SharedOptions.optDebug) contains DebugSectionTrees
    val debugTypes     = ctx.findOptionOrDefault(SharedOptions.optDebug) contains DebugSectionTypes
    val debugPositions = ctx.findOptionOrDefault(SharedOptions.optDebug) contains DebugSectionPositions

    PrinterOptions(
      baseIndent     = 0,
      printPositions = debugPositions,
      printUniqueIds = debugTrees,
      printTypes     = debugTypes
    )
  }
}
