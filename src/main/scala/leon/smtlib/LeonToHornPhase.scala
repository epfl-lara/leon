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
  
  override val definedOptions: Set[LeonOptionDef] = Set(      
    LeonValueOptionDef("outfilename", "--outfilename=<filename>", "name of the output file to dump horn clauses")    
  )

  def apply(ctx: LeonContext, program: Program) = {

    val reporter = ctx.reporter                 
    reporter.info("Running Horn clause generation Phase...")
    
    var outfilename = "horn-clauses.smt2" 
    var removeOrs = true

    for (opt <- ctx.options) opt match {
      case LeonValueOption("outfilename", ListValue(fs)) => {
        outfilename = fs(0)                
      }      
      case _ => ;
    }
    val outfile = new PrintWriter(outfilename)
    val t1 = System.currentTimeMillis()    
    val smtlibstr = new HornClausePrinter(program).toSmtLib
    outfile.print(smtlibstr)
    outfile.flush()
    outfile.close()
    val t2 = System.currentTimeMillis()
    reporter.info("Completed in "+(t2-t1)/1000.0+"s")
  }
}
