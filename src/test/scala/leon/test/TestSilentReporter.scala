/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test
import leon.{DefaultReporter,Settings}

class TestSilentReporter extends DefaultReporter(Settings()) {
  var lastErrors: List[String] = Nil

  override def emit(msg: Message): Unit = msg match { 
    case Message(this.ERROR, _, msg) => lastErrors ++= List(msg.toString)
    case Message(this.FATAL, _, msg) => lastErrors ++= List(msg.toString)
    case _ =>
  }
}
