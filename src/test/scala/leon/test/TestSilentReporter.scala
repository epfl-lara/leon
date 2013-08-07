package leon
package test

class TestSilentReporter extends DefaultReporter() {
  override def output(msg: String) : Unit = {}
}
