package leon

import purescala.Definitions._

class PassManager(passes: Seq[Pass]) {

  def run(program: Program): Program = {
    passes.foldLeft(program)((pgm, pass) => {
      Logger.debug("Running Pass: " + pass.description, 1, "passman")
      val newPgm = pass(pgm)
      Logger.debug("Resulting program: " + newPgm, 3, "passman")
      newPgm
    })
  }

}
