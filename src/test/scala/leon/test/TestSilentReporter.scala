/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package test

class TestSilentReporter extends DefaultReporter(Settings()) {
  var lastError: Option[String] = None

  override def emit(msg: Message): Unit = msg match { 
    case Message(this.ERROR, _, msg) => lastError = Some(msg.toString)
    case _ =>
  }
}
