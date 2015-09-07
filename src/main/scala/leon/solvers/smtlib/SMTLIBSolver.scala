/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import utils._
import purescala._
import Common._
import Expressions._
import Extractors._
import ExprOps._
import Types._
import Constructors._
import Definitions._

import _root_.smtlib.common._
import _root_.smtlib.printer.{RecursivePrinter => SMTPrinter}
import _root_.smtlib.parser.Commands.{Constructor => SMTConstructor, FunDef => _, Assert => SMTAssert, _}
import _root_.smtlib.parser.Terms.{
  Forall => SMTForall,
  Exists => SMTExists,
  Identifier => SMTIdentifier,
  Let => SMTLet,
  _
}
import _root_.smtlib.parser.CommandsResponses.{Error => ErrorResponse, _}
import _root_.smtlib.theories._
import _root_.smtlib.interpreters.ProcessInterpreter

abstract class SMTLIBSolver(val context: LeonContext,
                            val program: Program) extends Solver with SMTLIBTarget with NaiveAssumptionSolver {

  /* Solver name */
  def targetName: String
  override def name: String = "smt-"+targetName

  /* Reporter */
  protected val reporter = context.reporter

  /* Interface with Interpreter */

  protected def interpreterOps(ctx: LeonContext): Seq[String]

  protected def getNewInterpreter(ctx: LeonContext): ProcessInterpreter

  protected val interpreter = getNewInterpreter(context)


  /* Printing VCs */
  protected lazy val out: Option[java.io.FileWriter] = if (reporter.isDebugEnabled) Some {
    val file = context.files.headOption.map(_.getName).getOrElse("NA")
    val n    = VCNumbers.next(targetName+file)

    val dir = new java.io.File("smt-sessions")

    if (!dir.isDirectory) {
      dir.mkdir
    }

    val fileName = s"smt-sessions/$targetName-$file-$n.smt2"

    reporter.debug(s"Outputting smt session into $fileName" )

    val fw = new java.io.FileWriter(fileName, false)

    fw.write("; Solver : "+name+"\n")
    fw.write("; Options: "+interpreterOps(context).mkString(" ")+"\n")

    fw
  } else None


  /* Interruptible interface */

  private var interrupted = false

  context.interruptManager.registerForInterrupts(this)

  override def interrupt(): Unit = {
    interrupted = true
    interpreter.interrupt()
  }
  override def recoverInterrupt(): Unit = {
    interrupted = false
  }

  /* Send a command to the solver */
  def sendCommand(cmd: Command, rawOut: Boolean = false): CommandResponse = {
    out foreach { o =>
      SMTPrinter.printCommand(cmd, o)
      o.write("\n")
      o.flush()
    }
    interpreter.eval(cmd) match {
      case err@ErrorResponse(msg) if !hasError && !interrupted && !rawOut =>
        reporter.warning(s"Unexpected error from $name solver: $msg")
        // Store that there was an error. Now all following check()
        // invocations will return None
        addError()
        err
      case res => res
    }
  }

  def emit(s: SExpr): Unit = {
    out foreach { o =>
      SMTPrinter.printSExpr(s, o)
      o.write("\n")
      o.flush()
    }

    SMTPrinter.printSExpr(s, interpreter.in)
    interpreter.in.write("\n")
    interpreter.in.flush()
  }


  /* Public solver interface */

  def free() = {
    interpreter.free()
    context.interruptManager.unregisterForInterrupts(this)
    out foreach { _.close }
  }

  override def assertCnstr(expr: Expr): Unit = if(!hasError) {
    variablesOf(expr).foreach(declareVariable)
    try {
      val term = toSMT(expr)(Map())
      sendCommand(SMTAssert(term))
    } catch {
      case _ : SolverUnsupportedError =>
        // Store that there was an error. Now all following check()
        // invocations will return None
        addError()
    }
  }

  override def reset() = {
    sendCommand(Reset(), rawOut = true) match {
      case ErrorResponse(msg) =>
        reporter.warning(s"Failed to reset $name: $msg")
        throw new CantResetException(this)
      case _ =>
    }
  }

  override def check: Option[Boolean] = {
    if (hasError) None
    else sendCommand(CheckSat()) match {
      case CheckSatStatus(SatStatus)     => Some(true)
      case CheckSatStatus(UnsatStatus)   => Some(false)
      case CheckSatStatus(UnknownStatus) => None
      case e                             => None
    }
  }

  protected def getModel(filter: Identifier => Boolean): Map[Identifier, Expr] = {
    val syms = variables.aSet.filter(filter).toList.map(variables.aToB)
    if (syms.isEmpty) {
      Map()
    } else {
      val cmd: Command = GetValue(
        syms.head,
        syms.tail.map(s => QualifiedIdentifier(SMTIdentifier(s)))
      )

      sendCommand(cmd) match {
        case GetValueResponseSuccess(valuationPairs) =>

          valuationPairs.collect {
            case (SimpleSymbol(sym), value) if variables.containsB(sym) =>
              val id = variables.toA(sym)

              (id, fromSMT(value, id.getType)(Map(), Map()))
          }.toMap
        case _ =>
          Map() //FIXME improve this
      }
    }
  }

  override def getModel: Map[Identifier, Expr] = getModel( _ => true)

  override def push(): Unit = {
    constructors.push()
    selectors.push()
    testers.push()
    variables.push()
    genericValues.push()
    sorts.push()
    functions.push()
    errors.push()
    sendCommand(Push(1))
  }

  override def pop(): Unit = {
    constructors.pop()
    selectors.pop()
    testers.pop()
    variables.pop()
    genericValues.pop()
    sorts.pop()
    functions.pop()
    errors.pop()

    sendCommand(Pop(1))
  }

}

// Unique numbers
private [smtlib] object VCNumbers extends UniqueCounter[String]
