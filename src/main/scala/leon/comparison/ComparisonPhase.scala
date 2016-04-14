package leon.comparison

import leon.OptionsHelpers._
import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
import leon.purescala.Common.Identifier
import leon.{LeonContext, OptionsHelpers, SharedOptions, SimpleLeonPhase}
import leon.purescala.Definitions.{FunDef, Program}
import leon.purescala.ExprOps
import leon.purescala.Expressions.{Let, MatchExpr, Passes, Variable, _}
import leon.utils.PreprocessingPhase
import leon.verification.VerificationReport

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"

  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    println("--------------")
    println("APPLY METHOD OF COMPARISONPHASE")
    println("--------------")

    println("--------------")
    println("FUNDEFS BASE")
    println("--------------")
    val comparisonBase = ComparisonBase(ctx, "testcases/comparison/base")
    val listFunDef_base = comparisonBase.listFunDef
    listFunDef_base.map(println(_))

    println("--------------")
    println("FUNDEFS TO-COMPARE")
    println("--------------")
    val listFunDef = getFunDef(ctx, program)
    listFunDef.map(println(_))


    val compared = compare(listFunDef_base, listFunDef)

    println("retured pairs", compared.toString())



    ComparisonReport(comparisonBase, program, compared)
  }


  /**
    * This is the core of the phase, where each given function will be compared to the comparison bases FunDefs,
    * two by two
    * @param FunDefs_base
    * @param FunDefs
    * @return
    */
  def compare(FunDefs_base: List[FunDef], FunDefs: List[FunDef]): List[(FunDef, FunDef)] = {

    println("--------------")
    println("COMPARISON")
    println("--------------")

    // store all the similar function we find, between base and to-compare programs
    // later we will add some extra information (which part or which percentage is equal)
    val pairEqualFunDef =
      for{
        f1 <- FunDefs_base
        f2 <- FunDefs
        if(recursiveSearch(f1.body.get, f2.body.get))
      } yield {
        (f1, f2)
      }

    println("pair FunDef : ", pairEqualFunDef)


    pairEqualFunDef
  }

  def compareFunDef(f1: FunDef, f2: FunDef): Boolean = {

    println("f1 : ", f1.body.toString())
    println("f2 : ", f2.body.toString())

    val (normalizedBody1, map1) = ExprOps.normalizeStructure(f1.body.get)
    val (normalizedBody2, map2) = ExprOps.normalizeStructure(f2.body.get)

    println("normalizedBody1 : ", normalizedBody1, map1)
    println("normalizedBody2 : ", normalizedBody2, map2)

    if (normalizedBody1 == normalizedBody2) {
      println("true")
      true
    }
    else {
      println("false")
      false
    }
  }

  def treeCrowler(expr: Expr) = {
    expr match {
      case Lambda(args, _) => args.map(_.id)
      case Forall(args, _) => args.map(_.id)
      case LetDef(fds, _) => fds.flatMap(_.paramIds)
      case Let(i, _, _) => Seq(i)
      case MatchExpr(_, cses) => cses.flatMap(_.pattern.binders)
      case Passes(_, _, cses) => cses.flatMap(_.pattern.binders)
      case Variable(id) => Seq(id)
      case _ => Seq.empty[Identifier]
    }
  }

  def compareExpr(expr1: Expr, expr2: Expr): Boolean = {
    val (normalizedExpr1, _) = ExprOps.normalizeStructure(expr1)
    val (normalizedExpr2, _) = ExprOps.normalizeStructure(expr2)

    normalizedExpr1 == normalizedExpr2
  }

  def recursiveSearch(expr1: Expr, expr2: Expr): Boolean = {
    compareExpr(expr1, expr2)
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
