package leon
package comparison

import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.comparison.Utils._
import leon.utils.DebugSection

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"

  val comparators: List[Comparator] = List(
    ComparatorExprList,
    ComparatorClassList,
    ComparatorClassTree,
    ComparatorScoreTree,
    ComparatorDirectScoreTree
  )

  val comparatorsNames = comparators map (_.name)

  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    implicit val context = ctx


    val corpus = ComparisonCorpus(ctx, "testcases/comparison/corpus")
    val funDefsCorpus = corpus.funDefs
    val funDefs = getFunDef(ctx, program)


    // contain pair of function compared and score given by each comparator
    // a space is let for a comment string, for example size of common tree for DirectScoreTree comparator
    val comparison = combinationOfFunDef(funDefsCorpus, funDefs)

    val autocompletedHoles =
      funDefs filter hasHole map (fun => Completor.suggestCompletion(fun, corpus))

    ComparisonReport(ctx, program, corpus, comparatorsNames, comparison, autocompletedHoles)
  }


  /**
    * Compare each function from corpus to argument program
    *
    * @param funDefsCorpus
    * @param funDefs
    * @return
    */
  def combinationOfFunDef(funDefsCorpus: List[FunDef], funDefs: List[FunDef])
                         (implicit context: LeonContext) = {

    for {
      funDef <- funDefs
      funDefCorpus <- funDefsCorpus
      scores = comparators map (_.compare(funDefCorpus.body.get, funDef.body.get))
      if scores.map(_._1) exists (_ > 0.0)
    } yield {
      (funDef, funDefCorpus, scores)
    }
  }

  /**
    * Method inspired from VerficationPhase
    * A filter with undesirable FunDef added
    * Ensure that every FunDef has a body
    *
    * @param ctx
    * @param program
    * @return
    */
  def getFunDef(ctx: LeonContext, program: Program): List[FunDef] = {
    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"
    val filterFuns: Option[Seq[String]] = ctx.findOption(GlobalOptions.optFunctions)
    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher(program)), Some(excludeByDefault _))
    }

    val funDefs = program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos).tail

    funDefs filter { f =>
      f.qualifiedName(program) != "Ensuring.ensuring" &&
        f.qualifiedName(program) != "WebPage.apply" &&
        f.qualifiedName(program) != "Style" &&
        hasBody(f)
    }
  }

  def hasBody(funDef: FunDef): Boolean = funDef.body match {
    case Some(b) => true
    case None => false
  }


}
