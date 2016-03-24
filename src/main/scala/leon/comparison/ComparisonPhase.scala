package leon.comparison

import leon.OptionsHelpers._
import leon.{LeonContext, OptionsHelpers, SharedOptions, SimpleLeonPhase}
import leon.purescala.Definitions.{FunDef, Program}
import leon.verification.VerificationReport

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"


  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    println("you are in apply method of comparison")

    val listFunDef = getFunDef(ctx, program)
    
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

}
