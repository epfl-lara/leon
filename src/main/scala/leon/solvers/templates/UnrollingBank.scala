/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Printable
import purescala.Common._
import purescala.Expressions._
import purescala.Types._
import utils._

class UnrollingBank[T <% Printable](ctx: LeonContext, templateGenerator: TemplateGenerator[T]) extends IncrementalState {
  implicit val debugSection = utils.DebugSectionSolver
  implicit val ctx0 = ctx
  val reporter = ctx.reporter

  private val encoder = templateGenerator.encoder
  private val manager = templateGenerator.manager

  // Function instantiations have their own defblocker
  private val defBlockers    = new IncrementalMap[TemplateCallInfo[T], T]()
  private val lambdaBlockers = new IncrementalMap[TemplateAppInfo[T], T]()

  // Keep which function invocation is guarded by which guard,
  // also specify the generation of the blocker.
  private val callInfos     = new IncrementalMap[T, (Int, Int, T, Set[TemplateCallInfo[T]])]()
  private val appInfos      = new IncrementalMap[(T, App[T]), (Int, Int, T, T, Set[TemplateAppInfo[T]])]()
  private val appBlockers   = new IncrementalMap[(T, App[T]), T]()
  private val blockerToApps = new IncrementalMap[T, (T, App[T])]()
  private val functionVars  = new IncrementalMap[TypeTree, Set[T]]()

  def push() {
    callInfos.push()
    defBlockers.push()
    lambdaBlockers.push()
    appInfos.push()
    appBlockers.push()
    blockerToApps.push()
    functionVars.push()
  }

  def pop() {
    callInfos.pop()
    defBlockers.pop()
    lambdaBlockers.pop()
    appInfos.pop()
    appBlockers.pop()
    blockerToApps.pop()
    functionVars.pop()
  }

  def clear() {
    callInfos.clear()
    defBlockers.clear()
    lambdaBlockers.clear()
    appInfos.clear()
    appBlockers.clear()
    blockerToApps.clear()
    functionVars.clear()
  }

  def reset() {
    callInfos.reset()
    defBlockers.reset()
    lambdaBlockers.reset()
    appInfos.reset()
    appBlockers.reset()
    blockerToApps.clear()
    functionVars.reset()
  }

  def dumpBlockers() = {
    val generations = (callInfos.map(_._2._1).toSet ++ appInfos.map(_._2._1).toSet).toSeq.sorted

    generations.foreach { generation =>
      reporter.debug("--- " + generation)

      for ((b, (gen, origGen, ast, fis)) <- callInfos if gen == generation) {
        reporter.debug(f".     $b%15s ~> "+fis.mkString(", "))
      }

      for ((app, (gen, origGen, b, notB, infos)) <- appInfos if gen == generation) {
        reporter.debug(f".     $b%15s ~> "+infos.mkString(", "))
      }
    }
  }

  def satisfactionAssumptions = currentBlockers ++ manager.assumptions

  def refutationAssumptions = manager.assumptions

  def canUnroll = callInfos.nonEmpty || appInfos.nonEmpty

  def currentBlockers = callInfos.map(_._2._3).toSeq ++ appInfos.map(_._2._4).toSeq

  def getBlockersToUnlock: Seq[T] = {
    if (callInfos.isEmpty && appInfos.isEmpty) {
      Seq.empty
    } else {
      val minGeneration = (callInfos.values.map(_._1) ++ appInfos.values.map(_._1)).min
      val callBlocks = callInfos.filter(_._2._1 == minGeneration).toSeq.map(_._1) 
      val appBlocks = appInfos.values.filter(_._1 == minGeneration).toSeq.map(_._3)
      callBlocks ++ appBlocks
    }
  }

  private def registerCallBlocker(gen: Int, id: T, fis: Set[TemplateCallInfo[T]]) {
    val notId = encoder.mkNot(id)

    callInfos.get(id) match {
      case Some((exGen, origGen, _, exFis)) =>
        // PS: when recycling `b`s, this assertion becomes dangerous.
        // It's better to simply take the max of the generations.
        // assert(exGen == gen, "Mixing the same id "+id+" with various generations "+ exGen+" and "+gen)

        val minGen = gen min exGen

        callInfos += id -> (minGen, origGen, notId, fis++exFis)
      case None =>
        callInfos += id -> (gen, gen, notId, fis)
    }
  }

  private def registerAppBlocker(gen: Int, app: (T, App[T]), info: Set[TemplateAppInfo[T]]) : Unit = {
    appInfos.get(app) match {
      case Some((exGen, origGen, b, notB, exInfo)) =>
        val minGen = gen min exGen
        appInfos += app -> (minGen, origGen, b, notB, exInfo ++ info)

      case None =>
        val b = appBlockers.get(app) match {
          case Some(b) => b
          case None => encoder.encodeId(FreshIdentifier("b_lambda", BooleanType, true))
        }

        val notB = encoder.mkNot(b)
        appInfos += app -> (gen, gen, b, notB, info)
        blockerToApps += b -> app
    }
  }

  private def freshAppBlocks(apps: Traversable[(T, App[T])]) : Seq[T] = {
    apps.filter(!appBlockers.isDefinedAt(_)).toSeq.map { case app @ (blocker, App(caller, tpe, _)) =>

      val firstB = encoder.encodeId(FreshIdentifier("b_lambda", BooleanType, true))
      val freeEq = functionVars.getOrElse(tpe, Set()).toSeq.map(t => encoder.mkEquals(t, caller))
      val clause = encoder.mkImplies(encoder.mkNot(encoder.mkOr((freeEq :+ firstB) : _*)), encoder.mkNot(blocker))

      appBlockers += app -> firstB
      clause
    }
  }

  private def extendAppBlock(app: (T, App[T]), infos: Set[TemplateAppInfo[T]]) : T = {
    assert(!appInfos.isDefinedAt(app), "appInfo -= app must have been called to ensure blocker freshness")
    assert(appBlockers.isDefinedAt(app), "freshAppBlocks must have been called on app before it can be unlocked")
    assert(infos.nonEmpty, "No point in extending blockers if no templates have been unrolled!")

    val nextB = encoder.encodeId(FreshIdentifier("b_lambda", BooleanType, true))
    val extension = encoder.mkOr((infos.map(_.equals).toSeq :+ nextB) : _*)
    val clause = encoder.mkEquals(appBlockers(app), extension)

    appBlockers += app -> nextB
    clause
  }

  def getClauses(expr: Expr, bindings: Map[Expr, T]): Seq[T] = {
    // OK, now this is subtle. This `getTemplate` will return
    // a template for a "fake" function. Now, this template will
    // define an activating boolean...
    val template = templateGenerator.mkTemplate(expr)

    val trArgs = template.tfd.params.map(vd => Left(bindings(Variable(vd.id))))

    for (vd <- template.tfd.params if vd.getType.isInstanceOf[FunctionType]) {
      functionVars += vd.getType -> (functionVars.getOrElse(vd.getType, Set()) + bindings(vd.toVariable))
    }

    // ...now this template defines clauses that are all guarded
    // by that activating boolean. If that activating boolean is 
    // undefined (or false) these clauses have no effect...
    val (newClauses, callBlocks, appBlocks) = template.instantiate(template.start, trArgs)

    val blockClauses = freshAppBlocks(appBlocks.keys)

    for((b, infos) <- callBlocks) {
      registerCallBlocker(nextGeneration(0), b, infos)
    }

    for ((app, infos) <- appBlocks) {
      registerAppBlocker(nextGeneration(0), app, infos)
    }

    // ...so we must force it to true!
    val clauses = template.start +: (newClauses ++ blockClauses)

    reporter.debug("Generating clauses for: " + expr.asString)
    for (cls <- clauses) {
      reporter.debug("  . " + cls.asString(ctx))
    }

    clauses
  }

  def nextGeneration(gen: Int) = gen + 3

  def decreaseAllGenerations() = {
    for ((block, (gen, origGen, ast, infos)) <- callInfos) {
      // We also decrease the original generation here
      callInfos += block -> (math.max(1,gen-1), math.max(1,origGen-1), ast, infos)
    }

    for ((app, (gen, origGen, b, notB, infos)) <- appInfos) {
      appInfos += app -> (math.max(1,gen-1), math.max(1,origGen-1), b, notB, infos)
    }
  }

  def promoteBlocker(b: T) = {
    if (callInfos contains b) {
      val (_, origGen, ast, fis) = callInfos(b)
      
      callInfos += b -> (1, origGen, ast, fis)
    }

    if (blockerToApps contains b) {
      val app = blockerToApps(b)
      val (_, origGen, _, notB, infos) = appInfos(app)

      appInfos += app -> (1, origGen, b, notB, infos)
    }
  }

  def unrollBehind(ids: Seq[T]): Seq[T] = {
    assert(ids.forall(id => (callInfos contains id) || (blockerToApps contains id)))

    var newClauses : Seq[T] = Seq.empty

    val newCallInfos = ids.flatMap(id => callInfos.get(id).map(id -> _))
    callInfos --= ids

    val apps = ids.flatMap(id => blockerToApps.get(id))
    val thisAppInfos = apps.map(app => app -> {
      val (gen, _, _, _, infos) = appInfos(app)
      (gen, infos)
    })

    blockerToApps --= ids
    appInfos --= apps

    for ((app, (_, infos)) <- thisAppInfos if infos.nonEmpty) {
      val extension = extendAppBlock(app, infos)
      reporter.debug(" -> extending lambda blocker: " + extension)
      newClauses :+= extension
    }

    var fastAppInfos : Map[(T, App[T]), (Int, Set[TemplateAppInfo[T]])] = Map.empty

    for ((id, (gen, _, _, infos)) <- newCallInfos; info @ TemplateCallInfo(tfd, args) <- infos) {
      var newCls = Seq[T]()

      val defBlocker = defBlockers.get(info) match {
        case Some(defBlocker) =>
          // we already have defBlocker => f(args) = body
          defBlocker

        case None =>
          // we need to define this defBlocker and link it to definition
          val defBlocker = encoder.encodeId(FreshIdentifier("d", BooleanType))
          defBlockers += info -> defBlocker
          manager.implies(id, defBlocker)

          val template = templateGenerator.mkTemplate(tfd)
          //reporter.debug(template)

          val (newExprs, callBlocks, appBlocks) = template.instantiate(defBlocker, args)

          // we handle obvious appBlocks in an immediate manner in order to increase
          // performance for folds that just pass a lambda around to recursive calls
          val (fastApps, nextApps) = appBlocks.partition(p => p._2.toSeq match {
            case Seq(TemplateAppInfo(_, equals, _)) if equals == manager.trueT => true
            case _ => false
          })

          fastAppInfos ++= fastApps.mapValues(gen -> _)

          val blockExprs = freshAppBlocks(nextApps.keys)

          for((b, newInfos) <- callBlocks) {
            registerCallBlocker(nextGeneration(gen), b, newInfos)
          }

          for ((app, newInfos) <- nextApps) {
            registerAppBlocker(nextGeneration(gen), app, newInfos)
          }

          newCls ++= newExprs
          newCls ++= blockExprs
          defBlocker
      }

      // We connect it to the defBlocker:   blocker => defBlocker
      if (defBlocker != id) {
        newCls :+= encoder.mkImplies(id, defBlocker)
      }

      reporter.debug("Unrolling behind "+info+" ("+newCls.size+")")
      for (cl <- newCls) {
        reporter.debug("  . "+cl)
      }

      newClauses ++= newCls
    }

    for ((app @ (b, _), (gen, infos)) <- thisAppInfos ++ fastAppInfos; info @ TemplateAppInfo(template, equals, args) <- infos) {
      var newCls = Seq.empty[T]

      val lambdaBlocker = lambdaBlockers.get(info) match {
        case Some(lambdaBlocker) => lambdaBlocker

        case None =>
          val lambdaBlocker = encoder.encodeId(FreshIdentifier("d", BooleanType))
          lambdaBlockers += info -> lambdaBlocker
          manager.implies(b, lambdaBlocker)

          val (newExprs, callBlocks, appBlocks) = template.instantiate(lambdaBlocker, args)
          val blockExprs = freshAppBlocks(appBlocks.keys)

          for ((b, newInfos) <- callBlocks) {
            registerCallBlocker(nextGeneration(gen), b, newInfos)
          }

          for ((newApp, newInfos) <- appBlocks) {
            registerAppBlocker(nextGeneration(gen), newApp, newInfos)
          }

          newCls ++= newExprs
          newCls ++= blockExprs
          lambdaBlocker
      }

      val enabler = if (equals == manager.trueT) b else encoder.mkAnd(equals, b)
      newCls :+= encoder.mkImplies(enabler, lambdaBlocker)

      reporter.debug("Unrolling behind "+info+" ("+newCls.size+")")
      for (cl <- newCls) {
        reporter.debug("  . "+cl)
      }

      newClauses ++= newCls
    }

    /*
    for ((app @ (b, _), (gen, _, _, _, infos)) <- thisAppInfos if infos.isEmpty) {
      registerAppBlocker(nextGeneration(gen), app, infos)
    }
    */

    reporter.debug(s"   - ${newClauses.size} new clauses")
    //context.reporter.ifDebug { debug =>
    //  debug(s" - new clauses:")
    //  debug("@@@@")
    //  for (cl <- newClauses) {
    //    debug(""+cl)
    //  }
    //  debug("////")
    //}

    //dumpBlockers
    //readLine()

    newClauses
  }
}
