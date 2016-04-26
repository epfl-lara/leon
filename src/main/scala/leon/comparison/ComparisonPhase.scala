package leon.comparison

import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
import leon.{LeonContext, OptionsHelpers, SharedOptions, SimpleLeonPhase}
import leon.purescala.Definitions.{FunDef, Program}
import leon.purescala.{ExprOps, Expressions}
import leon.purescala.Expressions.{Let, MatchExpr, Passes, Variable, _}
import leon.purescala.Types.TypeParameter

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"

  val print = true

  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    val comparisonBase = ComparisonBase(ctx, "testcases/comparison/base")
    val listFunDef_base = comparisonBase.listFunDef.tail
    val listFunDef = getFunDef(ctx, program).tail

    println("---------")
    println("PROGRAM AND FUNDEF")
    println(program)
    println(listFunDef)
    println("----------")

    println("---------")
    println("compare the type tree of program")
    println("---------")
    println("base")
    println(program.classHierarchyRoots)
    println(program.classHierarchyRoots.last.knownCCDescendants)
    println(program.classHierarchyRoots.last.knownCCDescendants.head.tparams.head.tp)
    println(program.classHierarchyRoots.last.knownCCDescendants.head.tparams.head.tp.isInstanceOf[TypeParameter])
    println(program.classHierarchyRoots.last.knownCCDescendants.head.tparams.head.tp.getType)

    println("tocompare")
    println(comparisonBase.program.classHierarchyRoots)
    println(comparisonBase.program.classHierarchyRoots.last.knownCCDescendants)
    println(comparisonBase.program.classHierarchyRoots.last.knownCCDescendants.head.tparams.head.tp)
    println(comparisonBase.program.classHierarchyRoots.last.knownCCDescendants.head.tparams.head.tp.isInstanceOf[TypeParameter])
    println(comparisonBase.program.classHierarchyRoots.last.knownCCDescendants.head.tparams.head.tp.getType)

    println("---------")


    val compared = combinationOfFunDef(listFunDef_base, listFunDef)

    ComparisonReport(comparisonBase, program, compared)
  }


  /**
    * Compare each function from "base program" with "to-compare" program (the one given in argument)
    * @param FunDefs_base
    * @param FunDefs
    * @return
    */
  def combinationOfFunDef(FunDefs_base: List[FunDef], FunDefs: List[FunDef]) = {
    val pairEqualFunDef =
      for{
        funDef <- FunDefs
        funDef_base <- FunDefs_base
        percentageSimilarityList = ComparatorByList.compare(funDef_base.body.get, funDef.body.get)
        percentageSimilarityTree = ComparatorByTree.compare(funDef_base.body.get, funDef.body.get)
        //if(percentageSimilarityList > 0.0 || percentageSimilarityTree > 0.0)
      } yield {
        (funDef, funDef_base, percentageSimilarityList, percentageSimilarityTree)
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
