package leon.comparison

import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
import leon.{LeonContext, OptionsHelpers, SharedOptions, SimpleLeonPhase}
import leon.purescala.Definitions.{FunDef, Program}
import leon.purescala.{ExprOps, Expressions}
import leon.purescala.Expressions.{Let, MatchExpr, Passes, Variable, _}

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"

  val print = true

  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    val comparisonBase = ComparisonBase(ctx, "testcases/comparison/base")
    val listFunDef_base = comparisonBase.listFunDef
    val listFunDef = getFunDef(ctx, program)

    val compared = compare(listFunDef_base, listFunDef)

    ComparisonReport(comparisonBase, program, compared)
  }


  /**
    * Compare each function from "base program" with "to-compare" program (the one given in argument)
    * @param FunDefs_base
    * @param FunDefs
    * @return
    */
  def compare(FunDefs_base: List[FunDef], FunDefs: List[FunDef]): List[(FunDef, FunDef, Double)] = {

    if (print)
      println("--------------")
      println("COMPARISON")
      println("--------------")

    // store all the similar function we find, between base and to-compare programs
    // later we will add some extra information (which part or which percentage is equal)
    val pairEqualFunDef =
      for{
        funDef <- FunDefs
        funDef_base <- FunDefs_base
        percentageSimilarity = ComparatorByList.recursiveSearch(funDef_base.body.get, funDef.body.get)
        if(percentageSimilarity > 0.0)
      } yield {
        (funDef, funDef_base, percentageSimilarity)
      }

    pairEqualFunDef
  }






  /**
    * This method derives from VerificationPhase
    * Extract the list of function defined in a program
    * */
  def getFunDef(ctx : LeonContext, program: Program): List[FunDef] = {
    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"
    val filterFuns: Option[Seq[String]] = ctx.findOption(SharedOptions.optFunctions)
    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher(program)), Some(excludeByDefault _))
    }
    program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)
  }
}
