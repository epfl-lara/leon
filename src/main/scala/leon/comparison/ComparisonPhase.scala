package leon
package comparison

import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
import leon._
import leon.purescala.Definitions.{FunDef, Program}
import leon.purescala.{ExprOps, Expressions}
import leon.purescala.Expressions.{Let, MatchExpr, Passes, Variable, _}
import leon.purescala.Types.TypeParameter
import leon.synthesis.SynthesisSettings

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"

  var debug = false

  val comparators: List[Comparator] = List(
    ComparatorByExprList,
    ComparatorByClassList,
    ComparatorByClassTree,
    ComparatorByScoreTree,
    ComparatorDirectScoreTree
  )

  val comparatorsNames = comparators map (_.name)

  val print = false

  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    val debugFlag = ctx.findOption(GlobalOptions.optDebug)
    debug = if (debugFlag.isDefined) {
      ctx.reporter.info("Debug mode")
      true
    } else false


    val comparisonBase = ComparisonBase(ctx, "testcases/comparison/base/")
    val listFunDef_base = comparisonBase.listFunDef.tail
    val listFunDef = getFunDef(ctx, program).tail


    val compared = combinationOfFunDef(listFunDef_base, listFunDef)

    ComparisonReport(ctx, comparisonBase, program, comparatorsNames, compared)
  }




  /**
    * Compare each function from "base program" with "to-compare" program (the one given in argument)
 *
    * @param funDefs_base
    * @param funDefs
    * @return
    */
  def combinationOfFunDef(funDefs_base: List[FunDef], funDefs: List[FunDef]) = {

    for{
      funDef_base <- funDefs_base
      funDef <- funDefs
      scores = comparators map (_.compare(funDef_base.body.get, funDef.body.get))
      if scores.map(_._1) exists (_ > 0.0)
    } yield {
      (funDef, funDef_base, scores)
    }
  }






  /**
    * This method derives from VerificationPhase
    * Extract the list of function defined in a program
    * */
  def getFunDef(ctx : LeonContext, program: Program): List[FunDef] = {
    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"
    val filterFuns: Option[Seq[String]] = ctx.findOption(GlobalOptions.optFunctions)
    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher(program)), Some(excludeByDefault _))
    }
    program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)
  }
}
