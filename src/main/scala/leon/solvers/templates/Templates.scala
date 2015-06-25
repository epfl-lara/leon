/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import purescala.Definitions._

case class App[T](caller: T, tpe: FunctionType, args: Seq[T]) {
  override def toString = "(" + caller + " : " + tpe + ")" + args.mkString("(", ",", ")")
}

object Instantiation {
  type Clauses[T] = Seq[T]
  type CallBlockers[T] = Map[T, Set[TemplateCallInfo[T]]]
  type AppBlockers[T] = Map[(T, App[T]), Set[TemplateAppInfo[T]]]
  type Instantiation[T] = (Clauses[T], CallBlockers[T], AppBlockers[T])

  def empty[T] = (Seq.empty[T], Map.empty[T, Set[TemplateCallInfo[T]]], Map.empty[(T, App[T]), Set[TemplateAppInfo[T]]])

  implicit class MapWrapper[A,B](map: Map[A,Set[B]]) {
    def merge(that: Map[A,Set[B]]): Map[A,Set[B]] = (map.keys ++ that.keys).map { k =>
      k -> (map.getOrElse(k, Set.empty) ++ that.getOrElse(k, Set.empty))
    }.toMap
  }

  implicit class InstantiationWrapper[T](i: Instantiation[T]) {
    def ++(that: Instantiation[T]): Instantiation[T] = {
      val (thisClauses, thisBlockers, thisApps) = i
      val (thatClauses, thatBlockers, thatApps) = that

      (thisClauses ++ thatClauses, thisBlockers merge thatBlockers, thisApps merge thatApps)
    }
  }
}

import Instantiation.{empty => _, _}

trait Template[T] { self =>
  val encoder : TemplateEncoder[T]
  val manager : QuantificationManager[T]

  val start : T
  val args : Seq[T]
  val condVars : Map[Identifier, T]
  val exprVars : Map[Identifier, T]
  val clauses : Seq[T]
  val blockers : Map[T, Set[TemplateCallInfo[T]]]
  val applications : Map[T, Set[App[T]]]
  val quantifications: Seq[QuantificationTemplate[T]]
  val matchers: Map[T, Set[Matcher[T]]]
  val lambdas : Map[T, LambdaTemplate[T]]

  private var substCache : Map[Seq[T],Map[T,T]] = Map.empty

  def instantiate(aVar: T, args: Seq[T]): Instantiation[T] = {

    val baseSubstMap : Map[T,T] = substCache.get(args) match {
      case Some(subst) => subst
      case None =>
        val subst = (condVars ++ exprVars).map { case (id, idT) => idT -> encoder.encodeId(id) } ++
                    (this.args zip args)
        substCache += args -> subst
        subst
    }

    val lambdaSubstMap = lambdas.map { case (idT, lambda) => idT -> encoder.encodeId(lambda.id) }
    val quantificationSubstMap = quantifications.map(q => q.qs._2 -> encoder.encodeId(q.qs._1))
    val substMap : Map[T,T] = baseSubstMap ++ lambdaSubstMap ++ quantificationSubstMap + (start -> aVar)

    Template.instantiate(encoder, manager,
      clauses, blockers, applications, quantifications, matchers, lambdas, substMap)
  }

  override def toString : String = "Instantiated template"
}

object Template {

  private def functionCallInfos[T](encodeExpr: Expr => T)(expr: Expr): (Set[TemplateCallInfo[T]], Set[App[T]]) = {
    def invocationCaller(expr: Expr): Boolean = expr match {
      case fi: FunctionInvocation => true
      case Application(caller, _) => invocationCaller(caller)
      case _ => false
    }

    val calls = collect[Expr] {
      case IsTyped(f: FunctionInvocation, ft: FunctionType) => Set.empty
      case IsTyped(f: Application, ft: FunctionType) => Set.empty
      case f: FunctionInvocation => Set(f)
      case f: Application => Set(f)
      case _ => Set.empty
    }(expr)

    val (functionCalls, appCalls) = calls partition invocationCaller

    def functionTemplate(expr: Expr): TemplateCallInfo[T] = expr match {
      case FunctionInvocation(tfd, args) =>
        TemplateCallInfo(tfd, args.map(encodeExpr))
      case Application(caller, args) =>
        val TemplateCallInfo(tfd, prevArgs) = functionTemplate(caller)
        TemplateCallInfo(tfd, prevArgs ++ args.map(encodeExpr))
      case _ => scala.sys.error("Should never happen!")
    }

    val templates : Set[TemplateCallInfo[T]] = functionCalls map functionTemplate

    def applicationTemplate(expr: Expr): App[T] = expr match {
      case Application(caller : Application, args) =>
        val App(c, tpe, prevArgs) = applicationTemplate(caller)
        App(c, tpe, prevArgs ++ args.map(encodeExpr))
      case Application(c, args) =>
        App(encodeExpr(c), c.getType.asInstanceOf[FunctionType], args.map(encodeExpr))
      case _ => scala.sys.error("Should never happen!")
    }

    val apps : Set[App[T]] = appCalls map applicationTemplate

    (templates, apps)
  }

  private def selectMatchInfos[T](encodeExpr: Expr => T)(expr: Expr): Set[Matcher[T]] = {
    collect[Matcher[T]] {
      case ArraySelect(arr, index) =>
        Set(Matcher(encodeExpr(arr), arr.getType, Seq(encodeExpr(index))))
      case MapGet(map, key) =>
        Set(Matcher(encodeExpr(map), map.getType, Seq(encodeExpr(key))))
      case _ => Set.empty
    }(expr)
  }

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
    val Application(caller, arguments) = rec(FunctionInvocation(tfd, fiArgs), appArgs)
    Matcher(encodeExpr(caller), caller.getType, arguments.map(encodeExpr))
  }

  def encode[T](
    encoder: TemplateEncoder[T],
    pathVar: (Identifier, T),
    arguments: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Map[T, LambdaTemplate[T]],
    substMap: Map[Identifier, T] = Map.empty[Identifier, T],
    optCall: Option[TypedFunDef] = None,
    optApp: Option[(T, FunctionType)] = None
  ) : (Seq[T], Map[T, Set[TemplateCallInfo[T]]], Map[T, Set[App[T]]], Map[T, Set[Matcher[T]]], () => String) = {

    val idToTrId : Map[Identifier, T] = {
      condVars ++ exprVars + pathVar ++ arguments ++ substMap ++
      lambdas.map { case (idT, template) => template.id -> idT }
    }

    val encodeExpr : Expr => T = encoder.encodeExpr(idToTrId)

    val clauses : Seq[T] = (for ((b,es) <- guardedExprs; e <- es) yield {
      encodeExpr(Implies(Variable(b), e))
    }).toSeq

    val extractInfos    : Expr => (Set[TemplateCallInfo[T]], Set[App[T]]) = functionCallInfos(encodeExpr)
    val extractMatchers : Expr => Set[Matcher[T]]                         = selectMatchInfos(encodeExpr)

    val optIdCall = optCall.map(tfd => TemplateCallInfo[T](tfd, arguments.map(_._2)))
    val optIdApp = optApp.map { case (idT, tpe) => App(idT, tpe, arguments.map(_._2)) }

    val invocMatcher = optCall.filter(_.returnType.isInstanceOf[FunctionType])
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
          val (newFunInfos, newAppInfos) = extractInfos(e)
          funInfos ++= newFunInfos
          appInfos ++= newAppInfos
          matchInfos ++= extractMatchers(e)
        }

        val calls = funInfos -- optIdCall
        if (calls.nonEmpty) blockers += b -> calls

        val apps = appInfos -- optIdApp
        if (apps.nonEmpty) applications += b -> apps

        val matchs = matchInfos ++
          apps.map(app => Matcher(app.caller, app.tpe, app.args)) ++
          funInfos.flatMap {
            case info @ TemplateCallInfo(tfd, args) if Some(info) == optIdCall =>
              invocMatcher
            case _ => None
          }

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
      " * Lambdas            :\n" + lambdas.map { case (_, template) =>
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
    lambdas: Map[T, LambdaTemplate[T]],
    substMap: Map[T, T]
  ): Instantiation[T] = {

    val substituter : T => T = encoder.substitute(substMap)

    val newClauses = clauses.map(substituter)
    val newBlockers = blockers.map { case (b,fis) =>
      substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
    }

    var instantiation: Instantiation[T] = (newClauses, newBlockers, Map.empty)

    for ((idT, lambda) <- lambdas) {
      val newIdT = substituter(idT)
      val newTemplate = lambda.substitute(substMap)
      instantiation ++= manager.instantiateLambda(newIdT, newTemplate)
    }

    for ((b,apps) <- applications; bp = substituter(b); app <- apps) {
      val newApp = app.copy(caller = substituter(app.caller), args = app.args.map(substituter))
      instantiation ++= manager.instantiateApp(bp, newApp)
    }

    for ((b, matchs) <- matchers; bp = substituter(b); m <- matchs) {
      val newM = m.copy(caller = substituter(m.caller), args = m.args.map(substituter))
      instantiation ++= manager.instantiateMatcher(bp, newM)
    }

    for (q <- quantifications) {
      instantiation ++= q.instantiate(substMap)
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
    guardedExprs: Map[Identifier, Seq[Expr]],
    quantifications: Seq[QuantificationTemplate[T]],
    lambdas: Map[T, LambdaTemplate[T]],
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
      pathVar._2,
      arguments.map(_._2),
      condVars,
      exprVars,
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
  val start: T,
  val args: Seq[T],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val quantifications: Seq[QuantificationTemplate[T]],
  val matchers: Map[T, Set[Matcher[T]]],
  val lambdas: Map[T, LambdaTemplate[T]],
  isRealFunDef: Boolean,
  stringRepr: () => String) extends Template[T] {

  private lazy val str : String = stringRepr()
  override def toString : String = str

  override def instantiate(aVar: T, args: Seq[T]): (Seq[T], Map[T, Set[TemplateCallInfo[T]]], Map[(T, App[T]), Set[TemplateAppInfo[T]]]) = {
    if (!isRealFunDef) manager.registerFree(tfd.params.map(_.getType) zip args)
    super.instantiate(aVar, args)
  }
}

object LambdaTemplate {

  private var typedIds : Map[TypeTree, List[Identifier]] = Map.empty.withDefaultValue(List.empty)

  private def structuralKey[T](lambda: Lambda, dependencies: Map[Identifier, T]): (Lambda, Map[Identifier,T]) = {

    def closureIds(expr: Expr): Seq[Identifier] = {
      val allVars : Seq[Identifier] = foldRight[Seq[Identifier]] {
        (expr, idSeqs) => idSeqs.foldLeft(expr match {
          case Variable(id) => Seq(id)
          case _ => Seq.empty[Identifier]
        })((acc, seq) => acc ++ seq)
      } (expr)

      val vars = variablesOf(expr)
      allVars.filter(vars(_)).distinct
    }

    val grouped : Map[TypeTree, Seq[Identifier]] = (lambda.args.map(_.id) ++ closureIds(lambda)).groupBy(_.getType)
    val subst : Map[Identifier, Identifier] = grouped.foldLeft(Map.empty[Identifier,Identifier]) { case (subst, (tpe, ids)) =>
      val currentVars = typedIds(tpe)

      val freshCount = ids.size - currentVars.size
      val typedVars = if (freshCount > 0) {
        val allIds = currentVars ++ List.range(0, freshCount).map(_ => FreshIdentifier("x", tpe, true))
        typedIds += tpe -> allIds
        allIds
      } else {
        currentVars
      }

      subst ++ (ids zip typedVars)
    }

    val newArgs = lambda.args.map(vd => ValDef(subst(vd.id), vd.tpe))
    val newBody = replaceFromIDs(subst.mapValues(_.toVariable), lambda.body)
    val structuralLambda = Lambda(newArgs, newBody)

    val newDeps = dependencies.map { case (id, idT) => subst(id) -> idT }

    structuralLambda -> newDeps
  }

  def apply[T](
    ids: (Identifier, T),
    encoder: TemplateEncoder[T],
    manager: QuantificationManager[T],
    pathVar: (Identifier, T),
    arguments: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Map[T, LambdaTemplate[T]],
    baseSubstMap: Map[Identifier, T],
    dependencies: Map[Identifier, T],
    lambda: Lambda
  ) : LambdaTemplate[T] = {

    val id = ids._2
    val tpe = ids._1.getType.asInstanceOf[FunctionType]
    val (clauses, blockers, applications, matchers, templateString) =
      Template.encode(encoder, pathVar, arguments, condVars, exprVars, guardedExprs, lambdas,
        substMap = baseSubstMap + ids, optApp = Some(id -> tpe))

    val lambdaString : () => String = () => {
      "Template for lambda " + ids._1 + ": " + lambda + " is :\n" + templateString()
    }

    val (key, keyDeps) = structuralKey(lambda, dependencies)

    new LambdaTemplate[T](
      ids._1,
      encoder,
      manager,
      pathVar._2,
      arguments.map(_._2),
      condVars,
      exprVars,
      clauses,
      blockers,
      applications,
      matchers,
      lambdas,
      keyDeps,
      key,
      lambdaString
    )
  }
}

class LambdaTemplate[T] private (
  val id: Identifier,
  val encoder: TemplateEncoder[T],
  val manager: QuantificationManager[T],
  val start: T,
  val args: Seq[T],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val matchers: Map[T, Set[Matcher[T]]],
  val lambdas: Map[T, LambdaTemplate[T]],
  private[templates] val dependencies: Map[Identifier, T],
  private[templates] val structuralKey: Lambda,
  stringRepr: () => String) extends Template[T] {

  // Universal quantification is not allowed inside closure bodies!
  val quantifications: Seq[QuantificationTemplate[T]] = Seq.empty

  val tpe = id.getType.asInstanceOf[FunctionType]

  def substitute(substMap: Map[T,T]): LambdaTemplate[T] = {
    val substituter : T => T = encoder.substitute(substMap)

    val newStart = substituter(start)
    val newClauses = clauses.map(substituter)
    val newBlockers = blockers.map { case (b, fis) =>
      val bp = if (b == start) newStart else b
      bp -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
    }

    val newApplications = applications.map { case (b, fas) =>
      val bp = if (b == start) newStart else b
      bp -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
    }

    val newMatchers = matchers.map { case (b, ms) =>
      val bp = if (b == start) newStart else b
      bp -> ms.map(m => m.copy(caller = substituter(m.caller), args = m.args.map(substituter)))
    }

    val newLambdas = lambdas.map { case (idT, template) => idT -> template.substitute(substMap) }

    val newDependencies = dependencies.map(p => p._1 -> substituter(p._2))

    new LambdaTemplate[T](
      id,
      encoder,
      manager,
      newStart,
      args,
      condVars,
      exprVars,
      newClauses,
      newBlockers,
      newApplications,
      newMatchers,
      newLambdas,
      newDependencies,
      structuralKey,
      stringRepr
    )
  }

  private lazy val str : String = stringRepr()
  override def toString : String = str

  def contextEquality(that: LambdaTemplate[T]) : Option[Seq[T]] = {
    if (structuralKey != that.structuralKey) {
      None // can't be equal
    } else if (dependencies.isEmpty) {
      Some(Seq.empty) // must be equal
    } else {
      def rec(e1: Expr, e2: Expr): Seq[T] = (e1,e2) match {
        case (Variable(id1), Variable(id2)) =>
          if (dependencies.isDefinedAt(id1)) {
            Seq(encoder.mkEquals(dependencies(id1), that.dependencies(id2)))
          } else {
            Seq.empty
          }

        case (Operator(es1, _), Operator(es2, _)) =>
          (es1 zip es2).flatMap(p => rec(p._1, p._2))

        case _ => Seq.empty
      }

      Some(rec(structuralKey, that.structuralKey))
    }
  }
}
