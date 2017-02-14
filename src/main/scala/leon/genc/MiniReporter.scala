/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import utils.{ NoPosition, Position }

/*
 * The MiniReporter trait is a simple convinient trait that provides
 * overloading and shorthands for the usual reporter from LeonContext.
 *
 * The MiniReporter object simply provides a way to create an instance
 * of the same trait. It is useful if one whish to "import" the shorthands
 * into the current scope without using inheritance. E.g.:
 *
 * val reporter = MiniReporter(ctx)
 * import reporter._
 */

private[genc] object MiniReporter {
  def apply(ctx0: LeonContext) = new MiniReporter { val ctx = ctx0 }
}

private[genc] trait MiniReporter {

  protected val ctx: LeonContext

  def internalError(msg: String, cause: Throwable = null) = {
    import java.lang.Thread

    val stack = Thread.currentThread.getStackTrace

    debug(s"internal error `$msg` from:")
    for (s <- stack)
      debug(s.toString)

    if (cause != null) {
      debug("because of")
      debug(cause)
    }

    ctx.reporter.internalError(msg)
  }

  def fatalError(msg: String, pos: Position = NoPosition) = ctx.reporter.fatalError(pos, msg)

  def debugTree(title: String, tree: ir.IR#Tree) = {
    if (ctx.reporter.isDebugEnabled(utils.DebugSectionTrees)) {
      ctx.reporter.info("\n")
      ctx.reporter.info(utils.ASCIIHelpers.title(title))
      ctx.reporter.info("\n")
      ctx.reporter.info(tree.toString)
      ctx.reporter.info("\n")
    }
  }

  def debug(msg: String) = ctx.reporter.debug(msg)(utils.DebugSectionGenC)

  def debug(e: Throwable) {
    import java.io.{ StringWriter, PrintWriter }

    val msg = e.getMessage
    if (msg != null)
      debug(e.getMessage)

    val sw = new StringWriter();
    e.printStackTrace(new PrintWriter(sw));

    val stack = sw.toString();
    debug("Exception's stack trace:\n " + stack)

    val cause = e.getCause
    if (cause != null) {
      debug("because of")
      debug(cause)
    }
  }

  def debug(msg: String, tree: CAST.Tree): Unit = debug(msg + ": " + tree2String(tree) + " of " + tree.getClass)

  def debug(tree: CAST.Tree): Unit = debug(tree2String(tree) + " of " + tree.getClass)

  private def tree2String(tree: CAST.Tree): String = {
    val p = new CPrinter()
    p.print(tree)
    p.toString
  }

  def warning(msg: String, pos: Position = NoPosition) = ctx.reporter.warning(pos, msg)

}

