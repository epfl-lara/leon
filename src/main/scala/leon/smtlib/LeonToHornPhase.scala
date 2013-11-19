package leon
package smtlib

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers._
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.ListValue
import leon.Reporter
import leon.verification.DefaultTactic
import leon.verification.ExtendedVC
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.invariant._
import scala.collection.mutable.{Set => MutableSet}
import leon.purescala.ScalaPrinter
import leon.solvers.SimpleSolverAPI
import leon.solvers.SolverFactory
import leon.solvers.z3.UIFZ3Solver
import leon.verification.VerificationReport

/**
 * @author ravi
 * This phase generates horn clauses from a leon program. 
 */
object LeonToHornPhase extends UnitPhase[Program] {
  val name = "genHorn"
  val description = "Horn clause generation phase"
  val fls = BooleanLiteral(false)
  
  override val definedOptions: Set[LeonOptionDef] = Set(      
    LeonValueOptionDef("outfilename", "--outfilename=<filename>", "name of the output file to dump horn clauses"),
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,...")
  )

  def apply(ctx: LeonContext, program: Program) = {

    val reporter = ctx.reporter                 
    reporter.info("Running Horn clause generation Phase...")

    //val functionsToAnalyse: MutableSet[String] = MutableSet.empty
    var outfile = new PrintWriter("horn-clauses.smt")

    for (opt <- ctx.options) opt match {
//      case LeonValueOption("functions", ListValue(fs)) =>
//        functionsToAnalyse ++= fs

      case LeonValueOption("outfilename", ListValue(fs)) => {
        val name = fs(0)
        outfile = new PrintWriter("horn-clauses.smt")
      }      
      case _ =>
    }

    val t1 = System.currentTimeMillis()
    val smtlibstr = HornClausePrinter(program)
    outfile.print(smtlibstr)
    outfile.flush()
    outfile.close()
    val t2 = System.currentTimeMillis()   
  }
}
