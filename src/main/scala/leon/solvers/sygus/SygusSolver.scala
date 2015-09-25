/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package sygus

import utils._
import grammars._

import purescala.Common._
import purescala.Definitions._
import purescala.Types._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Expressions._

import scala.collection.mutable.ArrayBuffer

import synthesis.Problem

import leon.solvers.smtlib._

import _root_.smtlib.common._
import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.parser.CommandsResponses.{Error => _, _}
import _root_.smtlib.parser.Parser.UnexpectedEOFException

abstract class SygusSolver(val context: LeonContext, val program: Program, val p: Problem) extends SMTLIBTarget {
  implicit val ctx = context
  implicit val debugSection = leon.utils.DebugSectionSynthesis

  val reporter = context.reporter

  protected def unsupported(t: Tree, str: String): Nothing = {
    throw new Unsupported(t, str)
  }

  def checkSynth(): Option[Expr] = {

    emit(SList(SSymbol("set-logic"), SSymbol("ALL_SUPPORTED")))

    val constraintId = QualifiedIdentifier(SMTIdentifier(SSymbol("constraint")))

    val bindings = p.as.map(a => a -> (symbolToQualifiedId(id2sym(a)): Term)).toMap

    // declare inputs
    for (a <- p.as) {
      emit(SList(SSymbol("declare-var"), id2sym(a), toSMT(a.getType)))
      variables += a -> id2sym(a)
    }

    // declare outputs
    val xToFd = for (x <- p.xs) yield {
      val fd = new FunDef(x.freshen, Seq(), x.getType, p.as.map(a => ValDef(a)))

      val fsym = id2sym(fd.id)

      functions += fd.typed -> fsym

      // declare function to synthesize
      emit(SList(SSymbol("synth-fun"), id2sym(fd.id), SList(fd.params.map(vd => SList(id2sym(vd.id), toSMT(vd.getType))) :_*), toSMT(fd.returnType)))

      x -> fd
    }

    val xToFdCall = xToFd.toMap.mapValues(fd => FunctionInvocation(fd.typed, p.as.map(_.toVariable)))

    val synthPhi = replaceFromIDs(xToFdCall, p.phi)

    val constraint = implies(p.pc, synthPhi)

    emit(FunctionApplication(constraintId, Seq(toSMT(constraint)(bindings))))

    emit(SList(SSymbol("check-synth"))) // check-synth emits: success; unsat; fdef*

    // We currently cannot predict the amount of success we will get, so we read as many as possible
    try { 
      var lastRes = interpreter.parser.parseSExpr
      while(lastRes == SSymbol("success")) {
        lastRes = interpreter.parser.parseSExpr
      }

      lastRes match {
        case SSymbol("unsat") =>

          val solutions = (for (x <- p.xs) yield {
            interpreter.parser.parseCommand match {
              case DefineFun(SMTFunDef(name, params, retSort, body)) =>
                val res = fromSMT(body, sorts.toA(retSort))(Map(), Map())
                Some(res)
              case r =>
                reporter.warning("Unnexpected result from cvc4-sygus: "+r)
                None
            }
          }).flatten

          if (solutions.size == p.xs.size) {
            Some(tupleWrap(solutions))
          } else {
            None
          }

        case SSymbol("unknown") =>
          None

        case r =>
          reporter.warning("Unnexpected result from cvc4-sygus: "+r+" expected unsat")
          None
      }
    } catch { 
      case _: UnexpectedEOFException =>
        None
    }
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

