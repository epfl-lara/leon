/* Copyright 2009-2016 EPFL, Lausanne */

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

class TestErrorReporter extends DefaultReporter(Set()) {
  override def emit(msg: Message): Unit = msg match { 
    case Message(this.ERROR | this.FATAL, _, _) => super.emit(msg)
    case _ =>
  }
}
