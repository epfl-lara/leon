package leon
package test

class TestSilentReporter extends DefaultReporter(Settings()) {
  override def output(msg: String) : Unit = { }
}
