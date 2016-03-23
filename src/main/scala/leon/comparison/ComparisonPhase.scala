package leon.comparison

import leon.{LeonContext, SimpleLeonPhase}
import leon.purescala.Definitions.Program
import leon.verification.VerificationReport

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"

  override def apply(ctx: LeonContext, v: Program): Unit = {
    println("you are in apply method of comparison")
  }
}
