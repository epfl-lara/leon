/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test
import leon.DefaultReporter

class TestSilentReporter extends DefaultReporter(Set()) {
  var lastErrors: List[String] = Nil

  override def emit(msg: Message): Unit = msg match { 
    case Message(this.ERROR, _, msg) => lastErrors ++= List(msg.toString)
    case Message(this.FATAL, _, msg) => lastErrors ++= List(msg.toString)
    case _ =>
  }
}
