package leon

import purescala.Definitions._

class PassManager(passes: Seq[Pass]) {

  def run(program: Program): Program = {
    passes.foldLeft(program)((pgm, pass) => {
      println("Running Pass: " + pass.description)
      val newPgm = pass(pgm)
      println("Resulting program: " + newPgm)
      newPgm
    })
  }

}
