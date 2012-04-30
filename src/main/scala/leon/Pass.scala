package leon

import purescala.Definitions._

abstract class Pass {

  def apply(pgm: Program): Program

  val description: String


  //Maybe adding some dependency declaration and tree checking methods

}
