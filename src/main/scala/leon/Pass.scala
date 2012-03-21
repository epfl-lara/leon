package leon

import purescala.Definitions._

abstract class Pass {

  def apply(pgm: Program): Program

}
