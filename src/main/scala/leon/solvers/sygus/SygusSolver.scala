/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package sygus

import utils._
import grammars._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Types._
import purescala.ExprOps._
import purescala.Extractors._
import Expressions._
import Definitions.Program
import scala.language.implicitConversions
import scala.collection.mutable.ArrayBuffer

import synthesis._

import smtlib._

import _root_.smtlib.common._
import _root_.smtlib.interpreters._
import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.Parser
import _root_.smtlib.lexer.Lexer
import _root_.smtlib.printer._
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.parser.CommandsResponses._

abstract class SygusSolver(val context: LeonContext, val program: Program, val p: Problem) extends SMTLIBTarget {
  implicit val ctx = context
  implicit val debugSection = leon.utils.DebugSectionSynthesis

  val reporter = context.reporter

  def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--cegqi-si",
      "--lang", "sygus"
    )
  }

  def getNewInterpreter = {
    val opts = interpreterOps(context)
    new CVC4SygusInterpreter("cvc4", opts.toArray)
  }

  protected def unsupported(t: Tree, str: String): Nothing = {
    throw new Unsupported(t, str)
  }

  protected lazy val debugOut: Option[java.io.FileWriter] = if (reporter.isDebugEnabled) Some {
    val file = context.files.headOption.map(_.getName).getOrElse("NA")
    val n    = SygusNumbers.next(file)

    val dir = new java.io.File("smt-sessions")

    if (!dir.isDirectory) {
      dir.mkdir
    }

    val fileName = s"smt-sessions/sygus-$file-$n.sl"

    reporter.debug(s"Outputting smt session into $fileName" )

    val fw = new java.io.FileWriter(fileName, false)

    fw.write("; Options: "+interpreterOps(context).mkString(" ")+"\n")

    fw
  } else None

  val i: ProcessInterpreter = getNewInterpreter

  def emit(s: SExpr): Unit = {
    debugOut.foreach { o =>
      RecursivePrinter.printSExpr(s, o)
      o.write("\n")
      o.flush()
    }

    RecursivePrinter.printSExpr(s, i.in)
    i.in.write("\n")
    i.in.flush()
  }


  def checkSynth(): Option[Expr] = {
    val parser = new Parser(new Lexer(i.out))

    val out = p.xs.head
    val c   = FreshIdentifier("c")
    val fd  = new FunDef(c, Seq(), out.getType, p.as.map(a => ValDef(a)))

    val bindings = p.as.map(a => a -> (symbolToQualifiedId(id2sym(a)): Term)).toMap

    val constraintId = QualifiedIdentifier(SMTIdentifier(SSymbol("constraint")))

    emit(SList(SSymbol("set-logic"), SSymbol("LIA")))


    // declare function
    emit(SList(SSymbol("synth-fun"), id2sym(fd.id), SList(fd.params.map(vd => SList(id2sym(vd.id), toSMT(vd.getType))) :_*), toSMT(out.getType)))

    // declare inputs
    for (a <- p.as) {
      emit(SList(SSymbol("declare-var"), id2sym(a), toSMT(a.getType)))
      variables += a -> id2sym(a)
    }

    val synthPhi = replaceFromIDs(Map(out -> FunctionInvocation(fd.typed, p.as.map(_.toVariable))), p.phi)

    val TopLevelAnds(clauses) = synthPhi

    for(c <- clauses) {
      emit(FunctionApplication(constraintId, Seq(toSMT(c)(bindings))))
    }

    emit(SList(SSymbol("check-synth")))

    parser.parseCheckSatResponse match {
      case CheckSatStatus(UnsatStatus) =>
        parser.parseCommand match {
          case DefineFun(SMTFunDef(name, params, retSort, body)) =>
            val res = fromSMT(body, sorts.toA(retSort))(Map(), Map())
            Some(res)
          case r =>
            reporter.warning("Unnexpected result from cvc4-sygus: "+r)
            None
        }
      case r =>
        reporter.warning("Unnexpected result from cvc4-sygus: "+r)
        None
    }
  }
}

private [sygus] object SygusNumbers extends UniqueCounter[String]

class CVC4SygusInterpreter(executable: String, args: Array[String]) extends ProcessInterpreter(executable, args) {

  override def parseResponseOf(cmd: Command): CommandResponse = cmd match {
    case DefineFunsRec(funs, bodies) =>
      // CVC4 translates definefunsrec in three commands per function,
      // and thus emits 3x (success)
      val res = for (i <- 1 to funs.size*3) yield {
        parser.parseGenResponse
      }

      res.find(_ != Success).getOrElse(Success)

    case _ =>
      super.parseResponseOf(cmd)
  }
}



    //val g = BaseGrammar || OneOf(p.as.map(_.toVariable))

    //type Label = TypeTree

    //var defined = Map[Label, Identifier]()
    //var definitions = new ArrayBuffer[(Identifier, Seq[Expr])]()

    //def getLabel(l: Label): Identifier = defined.getOrElse(l, {
    //  val id = FreshIdentifier(l.getType.toString, l.getType)
    //  defined += l -> id

    //  val defs = g.getProductions(l).map { g =>
    //    g.builder(g.subTrees.map(getLabel(_).toVariable))
    //  }

    //  definitions += (id -> defs)

    //  id
    //})

    //// discover grammar
    //getLabel(out.getType)

    //val grammarBindings: Map[Identifier, Term] = defined.map{ case (_, id) =>
    //  id -> QualifiedIdentifier(SMTIdentifier(idToSymbol(id)))
    //}

    //// define grammar
    //val grammar = SList((for ((id, ds) <- definitions) yield {
    //  SList(idToSymbol(id), typeToSort(id.getType), SList(ds.map(d => smt.toSMT(d)(bindings++grammarBindings)): _*))
    //}).toList)

