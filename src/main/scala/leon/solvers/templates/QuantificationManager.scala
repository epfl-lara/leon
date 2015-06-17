package leon
package solvers
package templates

import purescala.Common._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._

import Instantiation._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

class QuantificationTemplate[T](
  val quantificationManager: QuantificationManager[T],
  val start: T,
  val qs: (Identifier, T),
  val holdVar: T,
  val guardVar: T,
  val quantifiers: Seq[(Identifier, T)],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val lambdas: Map[T, LambdaTemplate[T]]) {

  def instantiate(blocker: T): Instantiation[T] = {
    quantificationManager.instantiateQuantification(blocker, this)
  }
}

object QuantificationTemplate {
  def apply[T](
    encoder: TemplateEncoder[T],
    quantificationManager: QuantificationManager[T],
    pathVar: (Identifier, T),
    qs: (Identifier, T),
    holder: Identifier,
    guard: Identifier,
    quantifiers: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Map[T, LambdaTemplate[T]],
    subst: Map[Identifier, T]
  ): QuantificationTemplate[T] = {

    val holders: (Identifier, T) = holder -> encoder.encodeId(holder)
    val guards: (Identifier, T) = guard -> encoder.encodeId(guard)

    val (clauses, blockers, applications, _) =
      Template.encode(encoder, pathVar, quantifiers, condVars, exprVars, guardedExprs, lambdas,
        substMap = subst + holders + guards)

    new QuantificationTemplate[T](quantificationManager,
      pathVar._2, qs, holders._2, guards._2, quantifiers,
      condVars, exprVars, clauses, blockers, applications, lambdas)
  }
}

trait QuantificationManager[T] { self : LambdaManager[T] =>

  private val stdQuantifiers: MutableMap[TypeTree, Seq[T]] = MutableMap.empty
  private val quantified: MutableSet[T] = MutableSet.empty

  private def standardQuantifiers(tpe: TypeTree, count: Int): Seq[T] = {
    val quantifiers = stdQuantifiers.getOrElse(tpe, Seq.empty)
    val currentCount = quantifiers.size

    if (currentCount >= count) quantifiers.take(count) else {
      val newQuantifiers = List.range(0, currentCount - count).map(_ => encoder.encodeId(FreshIdentifier("x", tpe)))
      quantified ++= newQuantifiers

      val allQuantifiers = quantifiers ++ newQuantifiers
      stdQuantifiers(tpe) = allQuantifiers
      allQuantifiers
    }
  }

  private def freshQuantifierSubst: Map[T, T] = stdQuantifiers.flatMap { case (tpe, ids) =>
    ids zip List.range(0, ids.size).map(_ => encoder.encodeId(FreshIdentifier("x", tpe)))
  }.toMap

  private val nextHolder: () => T = {
    val id: Identifier = FreshIdentifier("ph", BooleanType)
    () => encoder.encodeId(id)
  }

  private type Bindings = Set[(Option[T], FunctionType, Int, T)]
  private var bindingsStack: List[Bindings] = List(Set.empty)
  private def bindings: Bindings = bindingsStack.head
  private def bindings_=(bs: Bindings): Unit = {
    bindingsStack = bs :: bindingsStack.tail
  }

  private var quantificationsStack: List[Seq[Quantification]] = List(Seq.empty)
  private def quantifications: Seq[Quantification] = quantificationsStack.head
  private def quantifications_=(qs: Seq[Quantification]): Unit = {
    quantificationsStack = qs :: quantificationsStack.tail
  }

  private var instantiatedAppsStack: List[Seq[(T, App[T], Map[T,T])]] = List(Seq.empty)
  private def instantiatedApps: Seq[(T, App[T], Map[T,T])] = instantiatedAppsStack.head
  private def instantiatedApps_=(ias: Seq[(T, App[T], Map[T,T])]): Unit = {
    instantiatedAppsStack = ias :: instantiatedAppsStack.tail
  }

  private def known(tpe: FunctionType, idT: T): Boolean = freeLambdas(tpe)(idT) || byID.isDefinedAt(idT)

  private class Quantification (
    var holdVar: T,
    val guardVar: T,
    val condVars: Map[Identifier, T],
    val exprVars: Map[Identifier, T],
    val clauses: Seq[T],
    val blockers: Map[T, Set[TemplateCallInfo[T]]],
    val applications: Map[T, Set[App[T]]],
    val lambdas: Map[T, LambdaTemplate[T]],
    val binders: Set[App[T]]) {

    def substitute(subst: Map[T, T]) = {
      val substituter = encoder.substitute(subst)

      new Quantification (
        holdVar, guardVar, condVars, exprVars,
        clauses map substituter,
        blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        },
        applications map { case (b, fas) =>
          substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
        },
        lambdas map { case (idT, template) => substituter(idT) -> template.substitute(subst) },
        binders map { case app @ App(caller, _, args) =>
          app.copy(caller = substituter(caller), args = args.map(substituter))
        }
      )
    }

    def instantiate(blocker: T, app: App[T], quantifierSubst: Map[T, T]): Instantiation[T] = {
      val App(caller, tpe, args) = app

      // Build a mapping from applications in the quantified statement to all potential concrete
      // applications previously encountered. Also make sure the current `app` is in the mapping
      // as other instantiations have been performed previously when the associated applications
      // were first encountered.
      val appMappings: List[List[(T, App[T], App[T])]] = binders.toList
        // 1. select an application in the quantified proposition for which the current app can
        //    be bound when generating the new constraints
        .filter(qapp => qapp.caller == caller || (qapp.tpe == tpe && !known(qapp.tpe, qapp.caller)))
        // 2. build the instantiation mapping associated to the chosen current application binding
        .flatMap { bindingApp => binders
          // 2.1. select all potential matches for each quantified application
          .map { case qapp @ App(qcaller, qtpe, qargs) =>
            if (qapp == bindingApp) {
              bindingApp -> Set(blocker -> app)
            } else {
              val instances = self.applications(qtpe).filter {
                case (b, app @ App(caller, _, _)) => qcaller == caller || !known(qtpe, caller)
              }

              // concrete applications can appear multiple times in the constraint, and this is also the case
              // for the current application for which we are generating the constraints
              val withApp = if (qcaller == caller || !known(tpe, caller)) instances + (blocker -> app) else instances

              // add quantified application to instances for constraints that depend on free variables
              // this also make sure that constraints that don't depend on all variables will also be instantiated
              // Note: we can use `blocker` here as the blocker since it is guaranteed true in this branch
              val withAll = withApp + (blocker -> qapp)

              qapp -> withAll
            }
          }
          // 2.2. based on the possible bindings for each quantified application, build a set of
          //      instantiation mappings that can be used to instantiate all necessary constraints
          .foldLeft[List[List[(T, App[T], App[T])]]] (List(Nil)) {
            case (mappings, (qapp, instances)) => instances.toList.flatMap {
              case (b, app) => mappings.map(mapping => mapping :+ (b, app, qapp))
            }
          }
        }

      var instantiation = Instantiation.empty[T]

      for (mapping <- appMappings) {
        var constraints: List[T] = Nil
        var subst: Map[T, T] = quantifierSubst

        for {
          (b, App(qcaller, _, qargs), App(caller, _, args)) <- mapping
          _ = constraints :+= b
          _ = if (qcaller != caller) constraints :+= encoder.mkEquals(qcaller, caller)
          (qarg, arg) <- (qargs zip args)
        } if (subst.isDefinedAt(qarg) || !quantified(qarg)) {
          constraints :+= encoder.mkEquals(qarg, arg)
        } else {
          subst += qarg -> arg
        }

        val enabler = if (constraints.size == 1) constraints.head else encoder.mkAnd(constraints : _*)
        val holder = nextHolder()

        val lambdaSubstMap = lambdas.map { case (idT, lambda) => idT -> encoder.encodeId(lambda.id) }
        val substMap = subst ++ lambdaSubstMap + (guardVar -> enabler) + (holdVar -> holder)
        val substituter = encoder.substitute(subst)

        val newClauses = enabler +: clauses.map(substituter)
        val newBlockers = blockers.map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        }

        val newApplications = applications.map { case (b, fas) =>
          substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
        }

        instantiation ++= (newClauses, newBlockers, Map.empty)

        for ((idT, lambda) <- lambdas) {
          val newIdT = substituter(idT)
          val newTemplate = lambda.substitute(substMap)
          instantiation ++= self.instantiateLambda(newIdT, newTemplate)
        }

        for ((b, apps) <- newApplications; app <- apps) {
          instantiation ++= self.instantiateApp(b, app)
        }

        holdVar = holder
      }

      instantiation
    }
  }

  def instantiateQuantification(blocker: T, template: QuantificationTemplate[T]): Instantiation[T] = {

    val quantification: Quantification = {
      val quantified = template.quantifiers.map(_._2).toSet

      val bindingApps: Set[App[T]] = {
        def rec(templates: Map[T, LambdaTemplate[T]]): Set[App[T]] = templates.flatMap {
          case (_, template) => template.applications.flatMap(_._2).toSet ++ rec(template.lambdas)
        }.toSet

        val allApps = template.applications.flatMap(_._2).toSet ++ rec(template.lambdas)
        for (app @ App(caller, tpe, args) <- allApps if args exists quantified) yield app
      }

      val q = new Quantification(
        template.holdVar,
        template.guardVar,
        template.condVars,
        template.exprVars,
        template.clauses,
        template.blockers,
        template.applications,
        template.lambdas,
        bindingApps
      )

      val tpeCounts   = template.quantifiers.groupBy(_._1.getType).mapValues(_.map(_._2).toSeq)
      val substMap    = tpeCounts.flatMap { case (tpe, idTs) => idTs zip standardQuantifiers(tpe, idTs.size) }.toMap
      q.substitute(substMap + (template.start -> blocker))
    }

    val quantifierSubst: Map[T,T] = freshQuantifierSubst

    var instantiation: Instantiation[T] = (quantification.clauses, quantification.blockers, Map.empty)
    for (q <- quantifications; (b, apps) <- quantification.applications; app <- apps) {
      instantiation ++= q.instantiate(b, app, quantifierSubst)
    }

    val qBindings: Bindings = quantification.binders.flatMap {
      case App(caller, tpe, args) => args.zipWithIndex.collect {
        case (qid, idx) if quantified(qid) =>
          (if (known(tpe, caller)) Some(caller) else None, tpe, idx, qid)
      }
    }

    val (callerBindings, typeBindings) = (bindings ++ qBindings).partition(_._1.isDefined)

    val callerMap: Map[(T, Int), Set[T]] = callerBindings.groupBy(p => (p._1.get, p._3)).mapValues(_.map(_._4))
    val typeMap: Map[(FunctionType, Int), Set[T]] = typeBindings.groupBy(p => (p._2, p._3)).mapValues(_.map(_._4))

    val pairs: Set[(T, T)] = qBindings.flatMap { case (optIdT, tpe, idx, q) =>
      val matches = typeMap(tpe -> idx) ++ optIdT.toSeq.flatMap(idT => callerMap(idT -> idx))
      matches.map(q2 => q -> q2)
    }

    val mappings: List[Map[T, T]] =
      pairs.groupBy(_._1).toSeq.foldLeft(List(Map.empty[T, T])) {
        case (mappings, (_, pairs)) => pairs.toList.flatMap(p => mappings.map(mapping => mapping + p))
      }

    val newQuantifications = for (mapping <- mappings) yield {
      val ph = nextHolder()

      val freshConds = quantification.condVars.map(p => p._1.freshen -> p._2)
      val freshExprs = quantification.exprVars.map(p => p._1.freshen -> p._2)

      val substMap: Map[T, T] = mapping ++
        (freshConds ++ freshExprs).map { case (id, idT) => idT -> encoder.encodeId(id) } ++
        quantification.lambdas.map { case (idT, template) => idT -> encoder.encodeId(template.id) }

      val substituter = encoder.substitute(substMap)

      new Quantification(ph, quantification.guardVar,
        freshConds mapValues substituter,
        freshExprs mapValues substituter,
        quantification.clauses map substituter,
        quantification.blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        },
        quantification.applications map { case (b, fas) =>
          substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
        },
        quantification.lambdas map { case (idT, template) => substituter(idT) -> template.substitute(mapping) },
        quantification.binders map { case app @ App(caller, _, args) =>
          app.copy(caller = substituter(caller), args = args.map(substituter))
        }
      )
    }

    val eqClause = {
      val holders = newQuantifications.map(_.holdVar)
      val newHolders = if (holders.size > 1) encoder.mkAnd(holders : _*) else holders.head
      encoder.mkEquals(template.qs._2, newHolders)
    }

    instantiation = (instantiation._1 :+ eqClause, instantiation._2, instantiation._3)

    instantiatedApps = for ((b, app, qSubst) <- instantiatedApps) yield {
      val nqSubst = if (qSubst.size == stdQuantifiers.map(_._2.size).sum) qSubst else {
        stdQuantifiers.flatMap { case (tpe, ids) =>
          val recent = ids.dropWhile(qSubst.isDefinedAt)
          recent zip recent.map(_ => encoder.encodeId(FreshIdentifier("x", tpe)))
        }.toMap
      }

      for (q <- newQuantifications) {
        instantiation ++= q.instantiate(b, app, nqSubst)
      }

      (b, app, nqSubst)
    }

    for ((b, apps) <- quantification.applications; app <- apps) {
      instantiatedApps :+= (b, app, quantifierSubst)
    }

    instantiation
  }

  override def instantiateApp(blocker: T, app: App[T]): Instantiation[T] = {
    val quantifierSubst: Map[T, T] = freshQuantifierSubst

    var instantiation = Instantiation.empty[T]
    for (q <- quantifications) {
      instantiation ++= q.instantiate(blocker, app, quantifierSubst)
    }

    instantiatedApps :+= (blocker, app, quantifierSubst)
    instantiation
  }

  /*
  private class QuantificationScope(
    val quantifiedApps: List[App[T]],
    val quantifiers: Map[Identifier, T],
    val condVars: Map[Identifier, T],
    val exprVars: Map[Identifier, T],
    val clauses: Seq[T],
    val blockers: Map[T, Set[TemplateCallInfo[T]]],
    val applications: Map[T, Set[App[T]]],
    val lambdas: Map[T, LambdaTemplate[T]],
    val res: Set[T]
  ) {
    def this() = this(Nil, Map.empty, Map.empty, Map.empty, Seq.empty, Map.empty, Map.empty, Map.empty, Set.empty)
    def this(scope: QuantificationScope) = this(
      scope.quantifiedApps,
      scope.quantifiers,
      scope.condVars,
      scope.exprVars,
      scope.clauses,
      scope.blockers,
      scope.applications,
      scope.lambdas,
      scope.res
    )

    lazy val quantified: Set[T] = quantifiers.values.toSet
    def free(tpe: FunctionType, idT: T): Boolean = res(idT) || freeLambdas(tpe)(idT)
  }

  private var scopes: List[QuantificationScope] = List(new QuantificationScope)
  private def scope: QuantificationScope = scopes.head

  override def push(): Unit = {
    self.push()

    val currentScope = scope
    scopes = new QuantificationScope(currentScope) :: scopes.tail
  }

  override def pop(lvl: Int): Unit = {
    self.pop(lvl)
    scopes = scopes.drop(lvl)
  }

  def registerQuantified(
    startVar: Identifier,
    quantifierVars: Seq[Identifier],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Map[T, LambdaTemplate[T]],
    subst: Map[Identifier, T],
    res: Option[T]
  ): Unit = {
    val currentScope = scope
    def free(tpe: FunctionType, idT: T): Boolean = currentScope.free(tpe, idT) || res.exists(_ == idT)

    val quantifiers: Seq[(Identifier, T)] = quantifierVars.map(id => id -> encoder.encodeId(id))
    val quantified: Set[T] = quantifiers.map(_._2).toSet
    val pathVar = startVar -> subst(startVar)
    val (clauses, blockers, apps, _) = Template.encode(encoder, pathVar, quantifiers, condVars, exprVars, guardedExprs, lambdas, subst)

    val bindingApps: Set[App[T]] = {
      def rec(templates: Map[T, LambdaTemplate[T]]): Set[App[T]] = templates.flatMap {
        case (_, template) => template.applications.flatMap(_._2).toSet ++ rec(template.lambdas)
      }.toSet

      val allApps = apps.flatMap(_._2).toSet
      for (app @ App(caller, tpe, args) <- (allApps ++ rec(lambdas)) if args exists quantified) yield app
    }

    val argumentBindings: Set[(Option[T], FunctionType, Int, T)] = bindingApps.flatMap {
      case App(caller, tpe, args) => args.zipWithIndex.collect {
        case (qid, idx) if quantified(qid) => (if (free(tpe, caller)) Some(caller) else None, tpe, idx, qid)
      }
    }

    val (callerBindings, typeBindings) = argumentBindings.partition(_._1.isDefined)

    val typeMap: Map[FunctionType, Set[(Int, T)]] = typeBindings.groupBy(_._2).mapValues(_.map(p => (p._3, p._4)))
    val typePairs: Seq[(T, T)] = typeMap.toSeq.flatMap {
      case (_, argBinds) => argBinds.groupBy(_._1).mapValues(_.map(_._2)).toSeq.flatMap {
        case (_, options) => options.flatMap(o1 => options.map(o2 => o1 -> o2))
      }
    }

    val callerPairs: Seq[(T, T)] = callerBindings.groupBy(p => (p._1.get, p._2)).toSeq.flatMap {
      case ((freeFunction, tpe), arguments) =>
        val callerIdentified: Set[(Int, T)] = arguments.map(p => (p._3, p._4))
        val typeIdentified: Set[(Int, T)] = typeMap.getOrElse(tpe, Set.empty)

        (callerIdentified ++ typeIdentified).groupBy(_._1).mapValues(_.map(_._2)).toSeq.flatMap {
          case (_, options) => options.flatMap(o1 => options.map(o2 => o1 -> o2))
        }
    }

    val filteredPairs: Set[(T, T)] = {
      def rec(
        mappings: Seq[(T, T)],
        result: Set[(T, T)]
      ): Set[(T, T)] = mappings match {
        case (p @ (x, y)) +: tail if !result(p) && !result(y -> x) => rec(tail, result + p)
        case p +: tail => rec(tail, result)
        case Seq() => result
      }

      rec(callerPairs ++ typePairs, Set.empty)
    }

    val mappings: List[Map[T, T]] =
      filteredPairs.groupBy(_._1).toSeq.foldLeft(List(Map.empty[T, T])) {
        case (mappings, (_, pairs)) => pairs.toList.flatMap(p => mappings.map(mapping => mapping + p))
      }

    val (allClauses, allBlockers, allApps, quantifiedApps) = {
      var allClauses  : Seq[T]                           = Seq.empty
      var allBlockers : Map[T, Set[TemplateCallInfo[T]]] = Map.empty.withDefaultValue(Set.empty)
      var allApps     : Map[T, Set[App[T]]]              = Map.empty.withDefaultValue(Set.empty)

      var quantifiedApps : Set[App[T]] = Set.empty

      for (mapping <- mappings) {
        val substituter = encoder.substitute(mapping)
        allClauses ++= clauses.map(substituter)

        blockers.foreach { case (b, fis) =>
          val bp = substituter(b)
          val fisp = fis.map(fi => fi.copy(args = fi.args.map(substituter)))
          allBlockers += bp -> (allBlockers(bp) ++ fisp)
        }

        apps.foreach { case (b, fas) =>
          val bp = substituter(b)
          val fasp = fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
          allApps += bp -> (allApps(bp) ++ fasp)
        }

        quantifiedApps ++= bindingApps.map { case app @ App(caller, _, args) =>
          app.copy(caller = substituter(caller), args = args.map(substituter))
        }
      }

      (allClauses, allBlockers, allApps, quantifiedApps)
    }

    scopes = new QuantificationScope(
      currentScope.quantifiedApps ++ quantifiedApps,
      currentScope.quantifiers ++ quantifiers,
      currentScope.condVars ++ condVars,
      currentScope.exprVars ++ exprVars,
      currentScope.clauses ++ allClauses,
      currentScope.blockers merge allBlockers,
      currentScope.applications merge allApps,
      currentScope.lambdas ++ lambdas,
      currentScope.res ++ res
    ) :: scopes.tail
  }

  override def instantiateApp(blocker: T, app: App[T]): Instantiation[T] = {
    val App(caller, tpe, args) = app
    val currentScope = scope
    import currentScope._

    // Build a mapping from applications in the quantified statement to all potential concrete
    // applications previously encountered. Also make sure the current `app` is in the mapping
    // as other instantiations have been performed previously when the associated applications
    // were first encountered.
    val appMappings: List[List[(App[T], App[T])]] = quantifiedApps
      // 1. select an application in the quantified proposition for which the current app can
      //    be bound when generating the new constraints
      .filter(qapp => qapp.caller == caller || (qapp.tpe == tpe && !free(qapp.tpe, qapp.caller)))
      // 2. build the instantiation mapping associated to the chosen current application binding
      .flatMap { bindingApp => quantifiedApps
        // 2.1. select all potential matches for each quantified application
        .map { case qapp @ App(qcaller, qtpe, qargs) =>
          if (qapp == bindingApp) {
            bindingApp -> Set(app)
          } else {
            val instances = self.applications(qtpe).collect {
              case (_, app @ App(caller, _, _)) if qcaller == caller || !free(qtpe, caller) => app
            }

            // concrete applications can appear multiple times in the constraint, and this is also the case
            // for the current application for which we are generating the constraints
            val withApp = if (qcaller == caller || !free(tpe, caller)) instances + app else instances

            // add quantified application to instances for constraints that depend on free variables
            // this also make sure that constraints that don't depend on all variables will also be instantiated
            val withAll = withApp + qapp

            qapp -> withAll
          }
        }
        // 2.2. based on the possible bindings for each quantified application, build a set of
        //      instantiation mappings that can be used to instantiate all necessary constraints
        .foldLeft[List[List[(App[T], App[T])]]] (List(Nil)) {
          case (mappings, (qapp, instances)) =>
            instances.toList.flatMap(app => mappings.map(mapping => mapping :+ (app -> qapp)))
        }
      }

    var instantiation = Instantiation.empty[T]

    for (mapping <- appMappings) {
      var constraints: List[T] = Nil
      var subst: Map[T, T] = Map.empty

      for {
        (App(qcaller, _, qargs), App(caller, _, args)) <- mapping
        _ = if (qcaller != caller) constraints :+= encoder.mkEquals(qcaller, caller)
        (qarg, arg) <- (qargs zip args)
      } if (subst.isDefinedAt(qarg) || !quantified(qarg)) {
        constraints :+= encoder.mkEquals(qarg, arg)
      } else {
        subst += qarg -> arg
      }

      // make sure we freshen quantified variables that haven't been bound by concrete calls
      subst ++= quantifiers.collect {
        case (id, idT) if !subst.isDefinedAt(idT) => idT -> encoder.encodeId(id)
      }

      val bp = encoder.encodeId(FreshIdentifier("qb", BooleanType))
      // TODO: empty `constraints`
      val enabler = encoder.mkEquals(bp, encoder.mkAnd(constraints : _*))

      val lambdaSubstMap = lambdas.map { case (idT, lambda) => idT -> encoder.encodeId(lambda.id) }
      val substMap = subst ++ lambdaSubstMap + (start -> enabler)
      val substituter = encoder.substitute(subst)

      val newClauses = enabler +: clauses.map(substituter)
      val newBlockers = blockers.map { case (b, fis) =>
        substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
      }

      val newApplications = currentScope.applications.map { case (b, fas) =>
        substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
      }

      instantiation ++= (newClauses, newBlockers, Map.empty)

      for ((idT, lambda) <- lambdas) {
        val newIdT = substituter(idT)
        val newTemplate = lambda.substitute(substMap)
        instantiation ++= instantiateLambda(newIdT, newTemplate)
      }

      for ((b, apps) <- newApplications; app <- apps) {
        instantiation ++= instantiateApp(b, app)
      }
    }

    instantiation
  }
  */
}
