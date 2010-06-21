package purescala

import purescala.Definitions._

abstract class Analyzer(reporter: Reporter)  {
  def analyze(program: Program)
}
