package setconstraints

import Trees._
import purescala.Definitions.Program
import purescala.Definitions.AbstractClassDef
import purescala.Reporter
import purescala.Extensions.Analyser

class Main(reporter: Reporter) extends Analyser(reporter) {
  val description: String = "Analyser for advanced type inference based on set constraints"
  override val shortDescription = "Set constraints"

  def analyse(pgm: Program) : Unit = {

    val (tpeVars, funVars) = LabelProgram(pgm)
    val cl2adt = ADTExtractor(pgm)

    val cnstr = CnstrtGen(pgm, Map(tpeVars.toList: _*), Map(funVars.toList: _*), Map(cl2adt.toList: _*))

    reporter.info("The constraints are:")
    reporter.info(PrettyPrinter(cnstr))

    val classes = pgm.definedClasses
    val form = classes.find(_.isInstanceOf[AbstractClassDef])

    val (Seq(fa), fr) = funVars(pgm.definedFunctions(0))
    /*
    val fixpoints = Seq(
      FixPoint(fa, cl2adt(form.get)), 
      FixPoint(fr, UnionType(Seq(
        ConstructorType("Or", Seq(fr, fr)), 
        ConstructorType("Not", Seq(fr))))))

    reporter.info("The least fixpoint is:")
    reporter.info(fixpoints.map(PrettyPrinter.apply))

    MatchAnalyzer(pgm, fixpoints, reporter)
    */
    null

  }

}
