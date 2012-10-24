package leon

import synthesis.SynthesisPhase
import plugin.ExtractionPhase

object Main {

  def computeLeonPhases: List[LeonPhase] = {
    List(
      List(
        ExtractionPhase
      ),
      if (Settings.transformProgram) {
        List(
          ArrayTransformation,
          EpsilonElimination,
          ImperativeCodeElimination,
          /*UnitElimination,*/
          FunctionClosure,
          /*FunctionHoisting,*/
          Simplificator
        )
      } else {
        Nil
      }
    ,
      if (Settings.synthesis) {
        List(
          SynthesisPhase
        )
      } else {
        Nil
      }
    ,
      if (!Settings.stopAfterTransformation) {
        List(
          AnalysisPhase
        )
      } else {
        Nil
      }
    ).flatten
  }

  def main(args : Array[String]) : Unit = {
    var ctx = LeonContext(options = args.toList)

    val phases = computeLeonPhases

    for ((phase, i) <- phases.zipWithIndex) {
      ctx.reporter.info("%2d".format(i)+": "+phase.name)
      ctx = phase.run(ctx)
    }
  }
}

