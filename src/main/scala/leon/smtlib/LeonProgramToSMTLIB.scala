package leon
package smtlib

import java.io._

import utils._
import purescala._
import purescala.Definitions._
import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._

import _root_.smtlib.sexpr.SExprs._
import _root_.smtlib.Commands.{ Command, Assert, NonStandardCommand }
import _root_.smtlib.{ PrettyPrinter => SMTPrinter }
import _root_.smtlib.CommandResponses.SExprResponse
import _root_.smtlib.CommandResponses._
import _root_.smtlib._

object LeonToSMTLIBPhase extends UnitPhase[Program] {
  val name = "genSMTLIB"
  val description = "SMTLIB generation phase"

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("outfilename", "--outfilename=<filename>", "name of the output SMTLIB file"))

  def apply(ctx: LeonContext, program: Program) = {

    val reporter = ctx.reporter
    reporter.info("Running SMTLIB generation Phase...")

    var outfilename = "smtlib"
    var removeOrs = true

    for (opt <- ctx.options) opt match {
      case LeonValueOption("outfilename", ListValue(fs)) => {
        outfilename = fs(0)
      }
      case _ => ;
    }
    val t1 = System.currentTimeMillis()
    new ProgramToSMTLIB(program, ctx).toSmtLib(outfilename)
    val t2 = System.currentTimeMillis()
    reporter.info("Completed in " + (t2 - t1) / 1000.0 + "s")
  }
}

class ProgramToSMTLIB(pgm: Program, ctx: LeonContext) {

  val smtlibDeclarations = new ExprToSMTLIB(ctx)
  var smtlibFuncBodies = List[Command]()
  var smtlibFuncSpec = List[Command]()
  val tru = BooleanLiteral(true)
  val fls = BooleanLiteral(false)

  def toSmtLib(filename: String) = {

    pgm.definedFunctions.filterNot((fd) =>
      (fd.annotations contains "verified")
        || (fd.annotations contains "library")).foreach((fd) => {

      if (fd.returnType == UnitType)
        throw new IllegalStateException("Return Type of function is unit: " + fd.id)
      assertFunction(fd)
    })

    val header = List(NonStandardCommand(SList(SSymbol("set-logic"), SSymbol("ALL_SUPPORTED"))))
    val trailer = List(NonStandardCommand(SList(SSymbol("check-sat"))))
    val writer = new PrintWriter(filename + ".smt2")

    def writeCmds(cmds: List[Command]) = cmds.foreach {
      case cmd =>
        SMTPrinter(cmd, writer)
        writer.println()
    }
    writeCmds(header)
    writer.println()
    writeCmds(smtlibDeclarations.getCommands)
    writer.println()
    writeCmds(List(NonStandardCommand(SComment("function definitions"))))
    writeCmds(smtlibFuncBodies)
    writer.println()
    writeCmds(List(NonStandardCommand(SComment("properties"))))
    writeCmds(smtlibFuncSpec)
    writer.println()
    writeCmds(trailer)
    writer.println()
    writer.flush()
    writer.close()
  }

  private def assertFunction(fd: FunDef) = {
    if (fd.hasBody) {
      val params = fd.params.map(_.id)
      val funInvoke = FunctionInvocation(TypedFunDef(fd, fd.tparams.map(_.tp)),
        params.map(_.toVariable))
      val defExpr = Equals(funInvoke, matchToIfThenElse(fd.body.get))
      //      /println("Defexpr: "+defExpr)
      val (_, sexpr) = smtlibDeclarations.toSExprAndDefinitions(defExpr)

      //universally quantify all parameters
      val varmap = smtlibDeclarations.target.variables
      val sparams = params.map(p => SList(varmap.getB(p).get, smtlibDeclarations.target.sorts.getB(p.getType).get))
      val quantSExpr = SList(SSymbol("forall"), SList(sparams.toList), sexpr)
      smtlibFuncBodies :+= Assert(quantSExpr)

      //assert that the specification holds
      if (fd.hasPostcondition) {
        val (resvar, postExpr) = fd.postcondition.get
        val defPost = replace(Map(resvar.toVariable -> funInvoke), postExpr)
        val defSpec = matchToIfThenElse(if (fd.hasPrecondition) {
          Implies(fd.precondition.get, defPost)
        } else
          defPost)
        val (_, sSpec) = smtlibDeclarations.toSExprAndDefinitions(defSpec)
        val quantSpec = SList(SSymbol("forall"), SList(sparams.toList), sSpec)
        smtlibFuncSpec :+= Assert(quantSpec)  
      }
    }
  }
}
