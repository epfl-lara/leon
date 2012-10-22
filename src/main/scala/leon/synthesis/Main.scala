package leon
package synthesis

object Main {
  def main(args : Array[String]) {
    val reporter = new DefaultReporter
    val solvers  = List(new TrivialSolver(reporter))

    new Synthesizer(reporter, solvers).test()
  }

}
