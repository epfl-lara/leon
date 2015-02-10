/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import evaluators._

case class App[T](caller: T, tpe: TypeTree, args: Seq[T]) {
  override def toString = {
    "(" + caller + " : " + tpe + ")" + args.mkString("(", ",", ")")
  }
}

trait Template[T] { self =>
  val encoder : TemplateEncoder[T]
  val lambdaManager : LambdaManager[T]

  val start : T
  val args : Seq[T]
  val condVars : Map[Identifier, T]
  val exprVars : Map[Identifier, T]
  val clauses : Seq[T]
  val blockers : Map[T, Set[TemplateCallInfo[T]]]
  val applications : Map[T, Set[App[T]]]
  val lambdas : Map[T, LambdaTemplate[T]]

  private var substCache : Map[Seq[T],Map[T,T]] = Map.empty

  def instantiate(aVar: T, args: Seq[T]): (Seq[T], Map[T, Set[TemplateCallInfo[T]]], Map[(T, App[T]), Set[TemplateAppInfo[T]]]) = {

    val baseSubstMap : Map[T,T] = substCache.get(args) match {
      case Some(subst) => subst
      case None =>
        val subst = (condVars ++ exprVars).map { case (id, idT) => idT -> encoder.encodeId(id) } ++
                    (this.args zip args)
        substCache += args -> subst
        subst
    }

    val lambdaSubstMap = lambdas.map { case (idT, lambda) => idT -> encoder.encodeId(lambda.id) }

    val substMap : Map[T,T] = baseSubstMap ++ lambdaSubstMap + (start -> aVar)
    val substituter : T => T = encoder.substitute(substMap)

    val newClauses = clauses.map(substituter)
    val newBlockers = blockers.map { case (b,fis) =>
      substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
    }

    val newApplications = applications.map { case (b,fas) =>
      substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
    }

    val (newLambdas, lambdaClauses) = lambdas.foldLeft((Map.empty[T,LambdaTemplate[T]], Seq.empty[T])) {
      case ((newLambdas, clauses), (idT, lambda)) =>
        val newIdT = substituter(idT)
        val newTemplate = lambda.substitute(substMap)
        val eqClauses = lambdaManager.equalityClauses(newIdT, newTemplate)
        (newLambdas + (newIdT -> newTemplate), clauses ++ eqClauses)
    }

    val (appClauses, appBlockers, appApps) = lambdaManager.instantiate(newApplications, newLambdas)

    val allClauses = newClauses ++ appClauses ++ lambdaClauses
    val allBlockers = (newBlockers.keys ++ appBlockers.keys).map { k =>
      k -> (newBlockers.getOrElse(k, Set.empty) ++ appBlockers.getOrElse(k, Set.empty))
    }.toMap

    (allClauses, allBlockers, appApps)
  }

  override def toString : String = "Instantiated template"
}

object Template {

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
    optApp: Option[(T, TypeTree)] = None
  ) : (Seq[T], Map[T, Set[TemplateCallInfo[T]]], Map[T, Set[App[T]]], () => String) = {

    val idToTrId : Map[Identifier, T] = {
      condVars ++ exprVars + pathVar ++ arguments ++ substMap ++
      lambdas.map { case (idT, template) => template.id -> idT }
    }

    val encodeExpr : Expr => T = encoder.encodeExpr(idToTrId) _

    val clauses : Seq[T] = (for ((b,es) <- guardedExprs; e <- es) yield {
      encodeExpr(Implies(Variable(b), e))
    }).toSeq

    val blockers : Map[Identifier, Set[TemplateCallInfo[T]]] = {
      val optIdCall = optCall.map(tfd => TemplateCallInfo[T](tfd, arguments.map(_._2)))

      Map((for ((b,es) <- guardedExprs) yield {
        val calls = es.flatMap(e => functionCallsOf(e).map { fi =>
          TemplateCallInfo[T](fi.tfd, fi.args.map(encodeExpr))
        }).toSet -- optIdCall

        if (calls.isEmpty) None else Some(b -> calls)
      }).flatten.toSeq : _*)
    }

    val encodedBlockers : Map[T, Set[TemplateCallInfo[T]]] = blockers.map(p => idToTrId(p._1) -> p._2)

    val applications : Map[Identifier, Set[App[T]]] = {
      val optIdApp = optApp.map { case (idT, tpe) => App(idT, tpe, arguments.map(_._2)) }

      Map((for ((b,es) <- guardedExprs) yield {
        val apps = es.flatMap(e => functionAppsOf(e).map { fa =>
          App[T](encodeExpr(fa.caller), fa.caller.getType, fa.args.map(encodeExpr))
        }).toSet -- optIdApp

        if (apps.isEmpty) None else Some(b -> apps)
      }).flatten.toSeq : _*)
    }

    val encodedApps : Map[T, Set[App[T]]] = applications.map(p => idToTrId(p._1) -> p._2)

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
      " * Lambdas            :\n" + lambdas.map { case (_, template) =>
        " +> " + template.toString.split("\n").mkString("\n    ")
      }.mkString("\n")
    }

    (clauses, encodedBlockers, encodedApps, stringRepr)
  }
}

object FunctionTemplate {

  def apply[T](
    tfd: TypedFunDef,
    encoder: TemplateEncoder[T],
    lambdaManager: LambdaManager[T],
    pathVar: (Identifier, T),
    arguments: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Map[T, LambdaTemplate[T]],
    isRealFunDef: Boolean
  ) : FunctionTemplate[T] = {
    
    val (clauses, blockers, applications, templateString) =
      Template.encode(encoder, pathVar, arguments, condVars, exprVars, guardedExprs, lambdas,
        optCall = Some(tfd))

    val funString : () => String = () => {
      "Template for def " + tfd.signature +
      "(" + tfd.params.map(a => a.id + " : " + a.tpe).mkString(", ") + ") : " +
      tfd.returnType + " is :\n" + templateString()
    }

    new FunctionTemplate[T](
      tfd,
      encoder,
      lambdaManager,
      pathVar._2,
      arguments.map(_._2),
      condVars,
      exprVars,
      clauses,
      blockers,
      applications,
      lambdas,
      isRealFunDef,
      funString
    )
  }

}

class FunctionTemplate[T] private(
  val tfd: TypedFunDef,
  val encoder: TemplateEncoder[T],
  val lambdaManager: LambdaManager[T],
  val start: T,
  val args: Seq[T],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val lambdas: Map[T, LambdaTemplate[T]],
  isRealFunDef: Boolean,
  stringRepr: () => String) extends Template[T] {

  private lazy val str : String = stringRepr()
  override def toString : String = str

  override def instantiate(aVar: T, args: Seq[T]): (Seq[T], Map[T, Set[TemplateCallInfo[T]]], Map[(T, App[T]), Set[TemplateAppInfo[T]]]) = {
    if (!isRealFunDef) lambdaManager.registerFree(tfd.params.map(_.tpe) zip args)
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
        val allIds = currentVars ++ List.range(0, freshCount).map(_ => FreshIdentifier("x", true).setType(tpe))
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
    lambdaManager: LambdaManager[T],
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
    val tpe = ids._1.getType
    val (clauses, blockers, applications, templateString) =
      Template.encode(encoder, pathVar, arguments, condVars, exprVars, guardedExprs, lambdas,
        substMap = baseSubstMap + ids, optApp = Some(id -> tpe))

    val lambdaString : () => String = () => {
      "Template for lambda " + ids._1 + ": " + lambda + " is :\n" + templateString()
    }

    val (key, keyDeps) = structuralKey(lambda, dependencies)

    new LambdaTemplate[T](
      ids._1,
      encoder,
      lambdaManager,
      pathVar._2,
      arguments.map(_._2),
      condVars,
      exprVars,
      clauses,
      blockers,
      applications,
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
  val lambdaManager: LambdaManager[T],
  val start: T,
  val args: Seq[T],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val lambdas: Map[T, LambdaTemplate[T]],
  private[templates] val dependencies: Map[Identifier, T],
  private val structuralKey: Lambda,
  stringRepr: () => String) extends Template[T] {

  val tpe = id.getType

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

    val newLambdas = lambdas.map { case (idT, template) => idT -> template.substitute(substMap) }

    val newDependencies = dependencies.map(p => p._1 -> substituter(p._2))

    new LambdaTemplate[T](
      id,
      encoder,
      lambdaManager,
      newStart,
      args,
      condVars,
      exprVars,
      newClauses,
      newBlockers,
      newApplications,
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

        case (NAryOperator(es1, _), NAryOperator(es2, _)) =>
          (es1 zip es2).flatMap(p => rec(p._1, p._2))

        case (BinaryOperator(e11, e12, _), BinaryOperator(e21, e22, _)) =>
          rec(e11, e21) ++ rec(e12, e22)

        case (UnaryOperator(ue1, _), UnaryOperator(ue2, _)) =>
          rec(ue1, ue2)

        case _ => Seq.empty
      }

      Some(rec(structuralKey, that.structuralKey))
    }
  }
}
