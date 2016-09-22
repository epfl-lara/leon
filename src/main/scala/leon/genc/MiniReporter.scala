/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

private[genc] trait MiniReporter {

  val ctx: LeonContext

  def internalError(msg: String) = {
    import java.lang.Thread

    val stack = Thread.currentThread.getStackTrace

    debug(s"internal error `$msg` from:")
    for (s <- stack)
      debug(s.toString)

    ctx.reporter.internalError(msg)
  }

  def fatalError(msg: String) = ctx.reporter.fatalError(msg)

  def debug(msg: String) = ctx.reporter.debug(msg)(utils.DebugSectionGenC)

  def debug(e: Throwable) {
    import java.io.{ StringWriter, PrintWriter }

    val sw = new StringWriter();
    e.printStackTrace(new PrintWriter(sw));

    val stack = sw.toString();

    debug(e.getMessage)
    debug("Exception's stack trace:\n " + stack)

    val cause = e.getCause
    if (cause != null) {
      debug("because of")
      debug(cause)
    }
  }

}

