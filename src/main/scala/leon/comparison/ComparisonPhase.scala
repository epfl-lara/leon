package leon
package comparison

import leon.purescala.Definitions.{FunDef, Program}

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

  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    val debugFlag = ctx.findOption(GlobalOptions.optDebug)
    debug = if (debugFlag.isDefined) {
      ctx.reporter.info("Debug mode")
      true
    } else false


    val corpus = ComparisonCorpus(ctx, "testcases/comparison/base/")
    val listFunDef_corpus = corpus.listFunDef.tail
    val listFunDef = getFunDef(ctx, program).tail


    // contain pair of function compared and score given by each comparator
    // a space is let for a comment string, for example size of common tree for DirectScoreTree comparator
    val comparison = combinationOfFunDef(listFunDef_corpus, listFunDef)

    ComparisonReport(ctx, program, corpus, comparatorsNames, comparison)
  }




  /**
    * Compare each function from corpus to argument program
    *
    * @param funDefs_corpus
    * @param funDefs
    * @return
    */
  def combinationOfFunDef(funDefs_corpus: List[FunDef], funDefs: List[FunDef]) = {

    for{
      funDef_corpus <- funDefs_corpus
      funDef <- funDefs
      scores = comparators map (_.compare(funDef_corpus.body.get, funDef.body.get))
      if scores.map(_._1) exists (_ > 0.0)
    } yield {
      (funDef, funDef_corpus, scores)
    }
  }






  /**
    * This method derives from VerificationPhase
    * Extract the list of function defined in a program
    */
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
