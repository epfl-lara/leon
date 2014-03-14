/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package test

class TestSilentReporter extends DefaultReporter(Settings()) {
  override def output(msg: String) : Unit = { }
}
