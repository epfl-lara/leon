package leon.comparison

import leon.OptionsHelpers._
import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
import leon.{LeonContext, OptionsHelpers, SharedOptions, SimpleLeonPhase}
import leon.purescala.Definitions.{FunDef, Program}
import leon.utils.PreprocessingPhase
import leon.verification.VerificationReport

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"


  def extractBaseToCompare(ctx: LeonContext, files: List[String]) = {
    val extraction = ClassgenPhase andThen ExtractionPhase andThen new PreprocessingPhase(false)
    val (_, prog) = extraction.run(ctx, files)

    getFunDef(ctx, prog)
  }

  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    println("you are in apply method of comparison")
    val listFunDef = getFunDef(ctx, program)

    val baseComparisonFunDef = ComparisonBase(List("testcases/synthesis/BinaryTree2.scala")).listFunDef

    val testcasesProg = extractBaseToCompare(ctx, List("testcases/synthesis/BinaryTree2.scala"))


    println("--------------")
    println("PRINT BASE PROG AND COMPARED PROG")
    println("--------------")
    println("listFunDef is : ", listFunDef.toString())
    println("And the first element is : ", listFunDef.tail.head.toString)

    println("tparam head is ", listFunDef.tail.head.tparams.toString())
    println("param head is ", listFunDef.tail.head.params.toString())
    println("return type is ", listFunDef.tail.head.returnType.toString)
    println("body head is", listFunDef.tail.head.fullBody.toString)

    println("tparam compared head is ", testcasesProg.tail.head.tparams.toString())
    println("param compared head is ", testcasesProg.tail.head.params.toString())
    println("return compared type is ", testcasesProg.tail.head.returnType.toString)
    println("body compared head is", testcasesProg.tail.head.fullBody.toString)

    println("we compare")

    val compared = compare(baseComparisonFunDef, listFunDef)

    println(compared.toString())

    ComparisonReport(program, listFunDef)
  }


  /*
  This method derives from VerificationPhase
  It's aim is to extract something from the program (FunDef) to begin working
   */
  def getFunDef(ctx : LeonContext, program: Program): List[FunDef] = {
    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"
    val filterFuns: Option[Seq[String]] = ctx.findOption(SharedOptions.optFunctions)
    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher(program)), Some(excludeByDefault _))
    }
    program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)
  }

  def compare(p1: List[FunDef], p2: List[FunDef]): List[(FunDef, FunDef)] = {
    for{
      f1 <- p1
      f2 <- p2
      if(f1.body == f2.body)
    } yield {
      (f1, f2)
    }
  }

  def compareFunDef(f1: FunDef, f2: FunDef): Boolean = {
    println("f1 ", f1.params.toString())
    println("f2 ", f2.params.toString())
    if (f1.tparams == f2.tparams) true
    else false
  }
}
