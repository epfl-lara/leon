/* Copyright 2009-2016 EPFL, Lausanne */

package leon.solvers.isabelle

import org.slf4j.{Logger, ILoggerFactory}
import org.slf4j.helpers.NOPLogger

import info.hupel.slf4j.DefaultLogger

import leon.Reporter
import leon.utils._

object LeonLoggerFactory {

  private implicit val debugSection = DebugSectionIsabelle

  private var _reporter: Option[Reporter] = None

  private[isabelle] def reporter_=(r: Reporter): Unit = _reporter = Some(r)

  private[isabelle] def reporter: Reporter = _reporter.getOrElse(sys.error("No reporter set"))

  private class LeonLogger extends DefaultLogger {
    import DefaultLogger._
    protected def writeLogMessage(level: LogLevel, message: Option[String], t: Option[Throwable] = None) {
      message.foreach { m =>
        level match {
          case TRACE => reporter.debug(m)
          case DEBUG => reporter.debug(m)
          case INFO =>  reporter.info(m)
          case WARN =>  reporter.warning(m)
          case ERROR => reporter.error(m)
        }
      }
      t.foreach(t => reporter.debug(t))
    }

  }

}

class LeonLoggerFactory extends ILoggerFactory {
  override def getLogger(name: String): Logger =
    if (name startsWith "edu.tum.cs.isabelle")
      new LeonLoggerFactory.LeonLogger
    else
      NOPLogger.NOP_LOGGER
}
