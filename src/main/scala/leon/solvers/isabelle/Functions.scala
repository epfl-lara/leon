package leon.solvers.isabelle

import scala.concurrent._
import scala.math.BigInt

import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.ExprOps
import leon.purescala.Types._
import leon.utils._

import edu.tum.cs.isabelle._

final class Functions(context: LeonContext, program: Program, types: Types, funs: List[FunDef], system: System)(implicit ec: ExecutionContext) {

  private implicit val debugSection = DebugSectionIsabelle
  private val strict = context.findOptionOrDefault(Component.optStrict)

  private val translator = new Translator(context, program, types, system)

  private val allLemmas = program.definedFunctions.flatMap(_.checkLemma(program, context)).toMap

  private def closure(funs: Set[FunDef]): Set[FunDef] = {
    val referenced = funs.flatMap(program.callGraph.transitiveCallees)
    val lemmas = allLemmas.filter(_._2.exists(referenced.contains)).keySet
    if (lemmas.subsetOf(funs) && referenced.subsetOf(funs))
      funs
    else {
      context.reporter.debug(s"Discovered relevant lemma(s): ${lemmas.map(_.qualifiedName(program)).mkString(", ")}")
      closure(funs ++ referenced ++ lemmas)
    }
  }

  private val relevant = closure(funs.toSet).toList

  private val preGroups = program.callGraph.stronglyConnectedComponents.map(_.filter(relevant.contains)).filterNot(_.isEmpty).toSet
  private val callGraph = preGroups.map { group => group ->
    preGroups.filter(cand => cand.exists(to => group.exists(from => program.callGraph.calls(from, to))) && cand != group)
  }.toMap

  private val groups = GraphOps.topologicalSorting(callGraph) match {
    case Right(seq) => seq.toList
    case Left(_) => context.reporter.internalError("unexpected cycle in call graph")
  }

  context.reporter.debug(s"Functions to be defined: ${groups.map(_.map(_.qualifiedName(program)).mkString("{", ", ", "}")).mkString(", ")}")

  private def globalLookup(data: List[FunDef])(fun: FunDef, typ: Typ) =
    if (data.contains(fun))
      Const(s"${theory}.${fun.id.mangledName}", typ)
    else
      context.reporter.internalError(s"Unknown function ${fun.qualifiedName(program)}")

  private def processGroup(group: Set[FunDef], data: List[FunDef]): Future[List[FunDef]] = {
    def lookup(fun: FunDef, typ: Typ): Term =
      if (group.contains(fun))
        Free(fun.id.mangledName, typ)
      else if (data.contains(fun))
        Const(s"${theory}.${fun.id.mangledName}", typ)
      else
        context.reporter.internalError(s"Unknown function ${fun.qualifiedName(program)} while defining functions")

    val defs = group.toList

    context.reporter.debug(s"Defining function(s) ${defs.map(_.qualifiedName(program)).mkString(", ")} ...")

    val pairs = defs.flatMap { fun =>
      val name = fun.qualifiedName(program)
      fun.extAnnotations.get("isabelle.function") match {
        case Some(List(Some(name: String))) => Some(fun -> (fun.id.mangledName -> name))
        case Some(List(_)) =>
          context.reporter.fatalError(s"In function mapping for function definition $name: expected a string literal as name")
        case Some(_) =>
          context.reporter.internalError(s"Function mapping for function definition $name")
        case None =>
          None
      }
    }

    system.invoke(Declare)(defs.map(_.id.mangledName)).assertSuccess(context).flatMap { case () => Future.traverse(defs) { fun =>
      val name = fun.id.mangledName
      val params = Future.traverse(fun.params.toList) { param =>
        types.typ(param.getType, strict = true).map(param.id.mangledName -> _)
      }

      val full = fun.annotations.contains("isabelle.fullBody")
      val none = fun.annotations.contains("isabelle.noBody")

      val body = (full, none) match {
        case (true, false) =>  translator.term(fun.fullBody, Nil, lookup)
        case (false, true) =>  translator.mkFreshError(None)
        case (false, false) => translator.term(fun.body.get, Nil, lookup)
        case (true, true) =>   context.reporter.fatalError(s"Conflicting body annotations for function definition ${fun.qualifiedName(program)}")
      }

      for {
        params <- params
        body <- body
        typ <- types.typ(fun.returnType, strict = true)
      }
      yield
        (name, params, (body, typ))
    }}.flatMap(system.invoke(Functions)).assertSuccess(context).flatMap {
      case Some(msg) => context.reporter.fatalError(s"In function definition: $msg")
      case None =>
        def requireProof(fun: FunDef) = funs.contains(fun) || strict

        val (checked, unchecked) = pairs.partition { case (fun, _) => requireProof(fun) }

        val equivalences =
          for {
            failed <- system.invoke(Equivalences)(checked.map(_._2)).assertSuccess(context)
            () <- system.invoke(AssumeEquivalences)(unchecked.map(_._2)).assertSuccess(context)
          }
          yield failed

        equivalences.foreach {
          case Nil => ()
          case failed => context.reporter.warning(s"Equivalence check(s) for ${failed.mkString(" and ")} failed")
        }
        equivalences.map(_ => data ++ defs)
    }.flatMap { data =>
      def generateStatement(fun: FunDef): Option[Future[(String, Term)]] =
        fun.statement.map(expr => translator.term(expr, Nil, globalLookup(data)).map(fun.id.mangledName -> _))

      val lemmas =
        Future.sequence(defs.filterNot(funs.contains).flatMap(generateStatement)).flatMap { statements =>
          if (strict)
            system.invoke(Lemmas)(statements).assertSuccess(context)
          else
            system.invoke(AssumeLemmas)(statements).assertSuccess(context).map(_ => Nil)
        }

      lemmas.foreach {
        case Nil => ()
        case failed => context.reporter.warning(s"Proof(s) of lemma(s) for ${failed.mkString(" and ")} failed")
      }

      lemmas.map(_ => data)
    }
  }

  val data: Future[List[FunDef]] =
    groups.foldLeft(Future.successful(List.empty[FunDef])) { (acc, group) =>
      acc.flatMap(processGroup(group, _))
    }

  def term(expr: Expr): Future[Term] = data.flatMap(data => translator.term(expr, Nil, globalLookup(data)))

}
