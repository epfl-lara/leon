/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

private[genc] trait SimpleReporter {

  val ctx: LeonContext

  def internalError(msg: String) = ctx.reporter.internalError(msg)
  def fatalError(msg: String)    = ctx.reporter.fatalError(msg)
  def debug(msg: String)         = ctx.reporter.debug(msg)(utils.DebugSectionGenC)

}

