/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Quantification._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import purescala.TypeOps._

import utils._

import scala.collection.generic.CanBuildFrom

object Instantiation {
  type Clauses[T] = Seq[T]
  type CallBlockers[T] = Map[T, Set[TemplateCallInfo[T]]]
  type AppBlockers[T] = Map[(T, App[T]), Set[TemplateAppInfo[T]]]
  type Instantiation[T] = (Clauses[T], CallBlockers[T], AppBlockers[T])

  def empty[T] = (Seq.empty[T], Map.empty[T, Set[TemplateCallInfo[T]]], Map.empty[(T, App[T]), Set[TemplateAppInfo[T]]])

  implicit class MapSetWrapper[A,B](map: Map[A,Set[B]]) {
    def merge(that: Map[A,Set[B]]): Map[A,Set[B]] = (map.keys ++ that.keys).map { k =>
      k -> (map.getOrElse(k, Set.empty) ++ that.getOrElse(k, Set.empty))
    }.toMap
  }

  implicit class MapSeqWrapper[A,B](map: Map[A,Seq[B]]) {
    def merge(that: Map[A,Seq[B]]): Map[A,Seq[B]] = (map.keys ++ that.keys).map { k =>
      k -> (map.getOrElse(k, Seq.empty) ++ that.getOrElse(k, Seq.empty))
    }.toMap
  }

  implicit class InstantiationWrapper[T](i: Instantiation[T]) {
    def ++(that: Instantiation[T]): Instantiation[T] = {
      val (thisClauses, thisBlockers, thisApps) = i
      val (thatClauses, thatBlockers, thatApps) = that

      (thisClauses ++ thatClauses, thisBlockers merge thatBlockers, thisApps merge thatApps)
    }

    def withClause(cl: T): Instantiation[T] = (i._1 :+ cl, i._2, i._3)
    def withClauses(cls: Seq[T]): Instantiation[T] = (i._1 ++ cls, i._2, i._3)

    def withCalls(calls: CallBlockers[T]): Instantiation[T] = (i._1, i._2 merge calls, i._3)
    def withApps(apps: AppBlockers[T]): Instantiation[T] = (i._1, i._2, i._3 merge apps)
    def withApp(app: ((T, App[T]), TemplateAppInfo[T])): Instantiation[T] = {
      (i._1, i._2, i._3 merge Map(app._1 -> Set(app._2)))
    }
  }
}

import Instantiation.{empty => _, _}

trait Template[T] { self =>
  val encoder : TemplateEncoder[T]
  val manager : QuantificationManager[T]

  val pathVar: (Identifier, T)
  val args : Seq[T]
  val condVars : Map[Identifier, T]
  val exprVars : Map[Identifier, T]
  val condTree : Map[Identifier, Set[Identifier]]
  val clauses : Seq[T]
  val blockers : Map[T, Set[TemplateCallInfo[T]]]
  val applications : Map[T, Set[App[T]]]
  val quantifications : Seq[QuantificationTemplate[T]]
  val matchers : Map[T, Set[Matcher[T]]]
  val lambdas : Seq[LambdaTemplate[T]]

  lazy val start = pathVar._2

  private var substCache : Map[Seq[T],Map[T,T]] = Map.empty

  def instantiate(aVar: T, args: Seq[T]): Instantiation[T] = {

    val baseSubstMap : Map[T,T] = substCache.get(args) match {
      case Some(subst) => subst
      case None =>
        val subst = exprVars.map { case (id, idT) => idT -> encoder.encodeId(id) } ++
                    manager.freshConds(pathVar._1 -> aVar, condVars, condTree) ++
                    (this.args zip args)
        substCache += args -> subst
        subst
    }

    val lambdaSubstMap = lambdas.map(lambda => lambda.ids._2 -> encoder.encodeId(lambda.ids._1))
    val quantificationSubstMap = quantifications.map(q => q.qs._2 -> encoder.encodeId(q.qs._1))
    val substMap : Map[T,T] = baseSubstMap ++ lambdaSubstMap ++ quantificationSubstMap + (start -> aVar)
    instantiate(substMap)
  }

  protected def instantiate(substMap: Map[T, T]): Instantiation[T] = {
    Template.instantiate(encoder, manager,
      clauses, blockers, applications, quantifications, matchers, lambdas, substMap)
  }

  override def toString : String = "Instantiated template"
}

object Template {

  private def invocationMatcher[T](encodeExpr: Expr => T)(tfd: TypedFunDef, args: Seq[Expr]): Matcher[T] = {
    assert(tfd.returnType.isInstanceOf[FunctionType], "invocationMatcher() is only defined on function-typed defs")

    def rec(e: Expr, args: Seq[Expr]): Expr = e.getType match {
      case FunctionType(from, to) =>
        val (appArgs, outerArgs) = args.splitAt(from.size)
        rec(Application(e, appArgs), outerArgs)
      case _ if args.isEmpty => e
      case _ => scala.sys.error("Should never happen")
    }

    val (fiArgs, appArgs) = args.splitAt(tfd.params.size)
    val app @ Application(caller, arguments) = rec(FunctionInvocation(tfd, fiArgs), appArgs)
    Matcher(encodeExpr(caller), bestRealType(caller.getType), arguments.map(arg => Left(encodeExpr(arg))), encodeExpr(app))
  }

  def encode[T](
    encoder: TemplateEncoder[T],
    pathVar: (Identifier, T),
    arguments: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Seq[LambdaTemplate[T]],
    substMap: Map[Identifier, T] = Map.empty[Identifier, T],
    optCall: Option[TypedFunDef] = None,
    optApp: Option[(T, FunctionType)] = None
  ) : (Seq[T], Map[T, Set[TemplateCallInfo[T]]], Map[T, Set[App[T]]], Map[T, Set[Matcher[T]]], () => String) = {

    val idToTrId : Map[Identifier, T] =
      condVars ++ exprVars + pathVar ++ arguments ++ substMap ++ lambdas.map(_.ids)

    val encodeExpr : Expr => T = encoder.encodeExpr(idToTrId)

    val clauses : Seq[T] = (for ((b,es) <- guardedExprs; e <- es) yield {
      encodeExpr(Implies(Variable(b), e))
    }).toSeq

    val optIdCall = optCall.map(tfd => TemplateCallInfo[T](tfd, arguments.map(_._2)))
    val optIdApp = optApp.map { case (idT, tpe) =>
      App(idT, bestRealType(tpe).asInstanceOf[FunctionType], arguments.map(_._2))
    }

    lazy val invocMatcher = optCall.filter(_.returnType.isInstanceOf[FunctionType])
      .map(tfd => invocationMatcher(encodeExpr)(tfd, arguments.map(_._1.toVariable)))

    val (blockers, applications, matchers) = {
      var blockers : Map[Identifier, Set[TemplateCallInfo[T]]] = Map.empty
      var applications : Map[Identifier, Set[App[T]]] = Map.empty
      var matchers : Map[Identifier, Set[Matcher[T]]] = Map.empty

      for ((b,es) <- guardedExprs) {
        var funInfos   : Set[TemplateCallInfo[T]] = Set.empty
        var appInfos   : Set[App[T]]              = Set.empty
        var matchInfos : Set[Matcher[T]]          = Set.empty

        for (e <- es) {
          funInfos ++= firstOrderCallsOf(e).map(p => TemplateCallInfo(p._1, p._2.map(encodeExpr)))
          appInfos ++= firstOrderAppsOf(e).map { case (c, args) =>
            App(encodeExpr(c), bestRealType(c.getType).asInstanceOf[FunctionType], args.map(encodeExpr))
          }

          matchInfos ++= fold[Map[Expr, Matcher[T]]] { (expr, res) =>
            val result = res.flatten.toMap

            result ++ (expr match {
              case QuantificationMatcher(c, args) =>
                // Note that we rely here on the fact that foldRight visits the matcher's arguments first,
                // so any Matcher in arguments will belong to the `result` map
                val encodedArgs = args.map(arg => result.get(arg) match {
                  case Some(matcher) => Right(matcher)
                  case None => Left(encodeExpr(arg))
                })

                Some(expr -> Matcher(encodeExpr(c), bestRealType(c.getType), encodedArgs, encodeExpr(expr)))
              case _ => None
            })
          }(e).values
        }

        val calls = funInfos -- optIdCall
        if (calls.nonEmpty) blockers += b -> calls

        val apps = appInfos -- optIdApp
        if (apps.nonEmpty) applications += b -> apps

        val matchs = matchInfos.filter { case m @ Matcher(mc, mtpe, margs, _) =>
          !optIdApp.exists { case App(ac, atpe, aargs) =>
            mc == ac && mtpe == atpe && margs.map(Matcher.argValue) == aargs
          }
        } ++ (if (funInfos.exists(info => Some(info) == optIdCall)) invocMatcher else None)

        if (matchs.nonEmpty) matchers += b -> matchs
      }

      (blockers, applications, matchers)
    }

    val encodedBlockers : Map[T, Set[TemplateCallInfo[T]]] = blockers.map(p => idToTrId(p._1) -> p._2)
    val encodedApps : Map[T, Set[App[T]]] = applications.map(p => idToTrId(p._1) -> p._2)
    val encodedMatchers : Map[T, Set[Matcher[T]]] = matchers.map(p => idToTrId(p._1) -> p._2)

    val stringRepr : () => String = () => {
      " * Activating boolean : " + pathVar._1 + "\n" +
      " * Control booleans   : " + condVars.keys.mkString(", ") + "\n" +
      " * Expression vars    : " + exprVars.keys.mkString(", ") + "\n" +
      " * Clauses            : " +
        (for ((b,es) <- guardedExprs; e <- es) yield (b + " ==> " + e)).mkString("\n   ") + "\n" +
      " * Invocation-blocks  :" + (if (blockers.isEmpty) "\n" else {
        "\n   " + blockers.map(p => p._1 + " ==> " + p._2).mkString("\n   ") + "\n"
      }) +
      " * Application-blocks :" + (if (applications.isEmpty) "\n" else {
        "\n   " + applications.map(p => p._1 + " ==> " + p._2).mkString("\n   ") + "\n"
      }) + 
      " * Matchers           :" + (if (matchers.isEmpty) "\n" else {
        "\n   " + matchers.map(p => p._1 + " ==> " + p._2).mkString("\n   ") + "\n"
      }) +
      " * Lambdas            :\n" + lambdas.map { case template =>
        " +> " + template.toString.split("\n").mkString("\n    ") + "\n"
      }.mkString("\n")
    }

    (clauses, encodedBlockers, encodedApps, encodedMatchers, stringRepr)
  }

  def instantiate[T](
    encoder: TemplateEncoder[T],
    manager: QuantificationManager[T],
    clauses: Seq[T],
    blockers: Map[T, Set[TemplateCallInfo[T]]],
    applications: Map[T, Set[App[T]]],
    quantifications: Seq[QuantificationTemplate[T]],
    matchers: Map[T, Set[Matcher[T]]],
    lambdas: Seq[LambdaTemplate[T]],
    substMap: Map[T, T]
  ): Instantiation[T] = {

    val substituter : T => T = encoder.substitute(substMap)

    val newClauses = clauses.map(substituter)
    val newBlockers = blockers.map { case (b,fis) =>
      substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
    }

    var instantiation: Instantiation[T] = (newClauses, newBlockers, Map.empty)

    for (lambda <- lambdas) {
      instantiation ++= manager.instantiateLambda(lambda.substitute(substituter))
    }

    for ((b,apps) <- applications; bp = substituter(b); app <- apps) {
      val newApp = app.copy(caller = substituter(app.caller), args = app.args.map(substituter))
      instantiation ++= manager.instantiateApp(bp, newApp)
    }

    for ((b, matchs) <- matchers; bp = substituter(b); m <- matchs) {
      instantiation ++= manager.instantiateMatcher(bp, m.substitute(substituter))
    }

    for (q <- quantifications) {
      instantiation ++= manager.instantiateQuantification(q, substMap)
    }

    instantiation
  }
}

object FunctionTemplate {

  def apply[T](
    tfd: TypedFunDef,
    encoder: TemplateEncoder[T],
    manager: QuantificationManager[T],
    pathVar: (Identifier, T),
    arguments: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    condTree: Map[Identifier, Set[Identifier]],
    guardedExprs: Map[Identifier, Seq[Expr]],
    quantifications: Seq[QuantificationTemplate[T]],
    lambdas: Seq[LambdaTemplate[T]],
    isRealFunDef: Boolean
  ) : FunctionTemplate[T] = {

    val (clauses, blockers, applications, matchers, templateString) =
      Template.encode(encoder, pathVar, arguments, condVars, exprVars, guardedExprs, lambdas,
        substMap = quantifications.map(q => q.qs).toMap,
        optCall = Some(tfd))

    val funString : () => String = () => {
      "Template for def " + tfd.signature +
      "(" + tfd.params.map(a => a.id + " : " + a.getType).mkString(", ") + ") : " +
      tfd.returnType + " is :\n" + templateString()
    }

    new FunctionTemplate[T](
      tfd,
      encoder,
      manager,
      pathVar,
      arguments.map(_._2),
      condVars,
      exprVars,
      condTree,
      clauses,
      blockers,
      applications,
      quantifications,
      matchers,
      lambdas,
      isRealFunDef,
      funString
    )
  }
}

class FunctionTemplate[T] private(
  val tfd: TypedFunDef,
  val encoder: TemplateEncoder[T],
  val manager: QuantificationManager[T],
  val pathVar: (Identifier, T),
  val args: Seq[T],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val condTree: Map[Identifier, Set[Identifier]],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val quantifications: Seq[QuantificationTemplate[T]],
  val matchers: Map[T, Set[Matcher[T]]],
  val lambdas: Seq[LambdaTemplate[T]],
  isRealFunDef: Boolean,
  stringRepr: () => String) extends Template[T] {

  private lazy val str : String = stringRepr()
  override def toString : String = str

  override def instantiate(aVar: T, args: Seq[T]): (Seq[T], Map[T, Set[TemplateCallInfo[T]]], Map[(T, App[T]), Set[TemplateAppInfo[T]]]) = {
    if (!isRealFunDef) manager.registerFree(tfd.params.map(_.id) zip args)
    super.instantiate(aVar, args)
  }
}

class TemplateManager[T](protected[templates] val encoder: TemplateEncoder[T]) extends IncrementalState {
  private val condImplies = new IncrementalMap[T, Set[T]].withDefaultValue(Set.empty)
  private val condImplied = new IncrementalMap[T, Set[T]].withDefaultValue(Set.empty)

  protected def incrementals: List[IncrementalState] = List(condImplies, condImplied)

  def clear(): Unit = incrementals.foreach(_.clear())
  def reset(): Unit = incrementals.foreach(_.reset())
  def push(): Unit = incrementals.foreach(_.push())
  def pop(): Unit = incrementals.foreach(_.pop())

  def freshConds(path: (Identifier, T), condVars: Map[Identifier, T], tree: Map[Identifier, Set[Identifier]]): Map[T, T] = {
    val subst = condVars.map { case (id, idT) => idT -> encoder.encodeId(id) }
    val mapping = condVars.mapValues(subst) + path

    for ((parent, children) <- tree; ep = mapping(parent); child <- children) {
      val ec = mapping(child)
      condImplies += ep -> (condImplies(ep) + ec)
      condImplied += ec -> (condImplied(ec) + ep)
    }

    subst
  }

  def blocker(b: T): Unit = condImplies += (b -> Set.empty)
  def isBlocker(b: T): Boolean = condImplies.isDefinedAt(b) || condImplied.isDefinedAt(b)
  
  def implies(b1: T, b2: T): Unit = implies(b1, Set(b2))
  def implies(b1: T, b2s: Set[T]): Unit = {
    val fb2s = b2s.filter(_ != b1)
    condImplies += b1 -> (condImplies(b1) ++ fb2s)
    for (b2 <- fb2s) {
      condImplied += b2 -> (condImplies(b2) + b1)
    }
  }

}
