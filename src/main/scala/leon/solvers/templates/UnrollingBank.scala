/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Expressions._
import purescala.Types._

class UnrollingBank[T](reporter: Reporter, templateGenerator: TemplateGenerator[T]) {
  implicit val debugSection = utils.DebugSectionSolver

  private val encoder = templateGenerator.encoder

  // Keep which function invocation is guarded by which guard,
  // also specify the generation of the blocker.
  private var callInfoStack = List[Map[T, (Int, Int, T, Set[TemplateCallInfo[T]])]](Map())
  private def callInfo = callInfoStack.head
  private def callInfo_= (v: Map[T, (Int, Int, T, Set[TemplateCallInfo[T]])]) = {
    callInfoStack = v :: callInfoStack.tail
  }

  // Function instantiations have their own defblocker
  private var defBlockersStack = List[Map[TemplateCallInfo[T], T]](Map.empty)
  private def defBlockers = defBlockersStack.head
  private def defBlockers_= (v: Map[TemplateCallInfo[T], T]) : Unit = {
    defBlockersStack = v :: defBlockersStack.tail
  }

  private var appInfoStack = List[Map[(T, App[T]), (Int, Int, T, T, Set[TemplateAppInfo[T]])]](Map())
  private def appInfo = appInfoStack.head
  private def appInfo_= (v: Map[(T, App[T]), (Int, Int, T, T, Set[TemplateAppInfo[T]])]) : Unit = {
    appInfoStack = v :: appInfoStack.tail
  }

  private var appBlockersStack = List[Map[(T, App[T]), T]](Map.empty)
  private def appBlockers = appBlockersStack.head
  private def appBlockers_= (v: Map[(T, App[T]), T]) : Unit = {
    appBlockersStack = v :: appBlockersStack.tail
  }

  private var blockerToAppStack = List[Map[T, (T, App[T])]](Map.empty)
  private def blockerToApp = blockerToAppStack.head
  private def blockerToApp_= (v: Map[T, (T, App[T])]) : Unit = {
    blockerToAppStack = v :: blockerToAppStack.tail
  }

  private var functionVarsStack = List[Map[TypeTree, Set[T]]](Map.empty.withDefaultValue(Set.empty))
  private def functionVars = functionVarsStack.head
  private def functionVars_= (v: Map[TypeTree, Set[T]]) : Unit = {
    functionVarsStack = v :: functionVarsStack.tail
  }

  def push() {
    appInfoStack = appInfo :: appInfoStack
    callInfoStack = callInfo :: callInfoStack
    defBlockersStack = defBlockers :: defBlockersStack
    blockerToAppStack = blockerToApp :: blockerToAppStack
    functionVarsStack = functionVars :: functionVarsStack
    appBlockersStack = appBlockers :: appBlockersStack
  }

  def pop(lvl: Int) {
    appInfoStack = appInfoStack.drop(lvl)
    callInfoStack = callInfoStack.drop(lvl)
    defBlockersStack = defBlockersStack.drop(lvl)
    blockerToAppStack = blockerToAppStack.drop(lvl)
    functionVarsStack = functionVarsStack.drop(lvl)
    appBlockersStack = appBlockersStack.drop(lvl)
  }

  def dumpBlockers() = {
    val generations = (callInfo.map(_._2._1).toSet ++ appInfo.map(_._2._1).toSet).toSeq.sorted

    generations.foreach { generation =>
      reporter.debug("--- " + generation)

      for ((b, (gen, origGen, ast, fis)) <- callInfo if gen == generation) {
        reporter.debug(f".     $b%15s ~> "+fis.mkString(", "))
      }

      for ((app, (gen, origGen, b, notB, infos)) <- appInfo if gen == generation) {
        reporter.debug(f".     $b%15s ~> "+infos.mkString(", "))
      }
    }
  }

  def canUnroll = callInfo.nonEmpty || appInfo.nonEmpty

  def currentBlockers = callInfo.map(_._2._3).toSeq ++ appInfo.map(_._2._4).toSeq

  def getBlockersToUnlock: Seq[T] = {
    if (callInfo.isEmpty && appInfo.isEmpty) {
      Seq.empty
    } else {
      val minGeneration = (callInfo.values.map(_._1) ++ appInfo.values.map(_._1)).min
      val callBlocks = callInfo.filter(_._2._1 == minGeneration).toSeq.map(_._1) 
      val appBlocks = appInfo.values.filter(_._1 == minGeneration).toSeq.map(_._3)
      callBlocks ++ appBlocks
    }
  }

  private def registerCallBlocker(gen: Int, id: T, fis: Set[TemplateCallInfo[T]]) {
    val notId = encoder.mkNot(id)

    callInfo.get(id) match {
      case Some((exGen, origGen, _, exFis)) =>
        // PS: when recycling `b`s, this assertion becomes dangerous.
        // It's better to simply take the max of the generations.
        // assert(exGen == gen, "Mixing the same id "+id+" with various generations "+ exGen+" and "+gen)

        val minGen = gen min exGen

        callInfo += id -> (minGen, origGen, notId, fis++exFis)
      case None =>
        callInfo += id -> (gen, gen, notId, fis)
    }
  }

  private def registerAppBlocker(gen: Int, app: (T, App[T]), info: Set[TemplateAppInfo[T]]) : Unit = {
    appInfo.get(app) match {
      case Some((exGen, origGen, b, notB, exInfo)) =>
        val minGen = gen min exGen
        appInfo += app -> (minGen, origGen, b, notB, exInfo ++ info)

      case None =>
        val b = appBlockers.get(app) match {
          case Some(b) => b
          case None => encoder.encodeId(FreshIdentifier("b_lambda", BooleanType, true))
        }

        val notB = encoder.mkNot(b)
        appInfo += app -> (gen, gen, b, notB, info)
        blockerToApp += b -> app
    }
  }

  private def freshAppBlocks(apps: Traversable[(T, App[T])]) : Seq[T] = {
    apps.filter(!appBlockers.isDefinedAt(_)).toSeq.map { case app @ (blocker, App(caller, tpe, _)) =>

      val firstB = encoder.encodeId(FreshIdentifier("b_lambda", BooleanType, true))
      val freeEq = functionVars(tpe).toSeq.map(t => encoder.mkEquals(t, caller))
      val clause = encoder.mkImplies(encoder.mkNot(encoder.mkOr((freeEq :+ firstB) : _*)), encoder.mkNot(blocker))

      appBlockers += app -> firstB
      clause
    }
  }

  private def extendAppBlock(app: (T, App[T]), infos: Set[TemplateAppInfo[T]]) : T = {
    assert(!appInfo.isDefinedAt(app), "appInfo -= app must have been called to ensure blocker freshness")
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

    val trArgs = template.tfd.params.map(vd => bindings(Variable(vd.id)))

    for (vd <- template.tfd.params if vd.getType.isInstanceOf[FunctionType]) {
      functionVars += vd.getType -> (functionVars(vd.getType) + bindings(vd.toVariable))
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

    reporter.debug("Generating clauses for: " + expr)
    for (cls <- clauses) {
      reporter.debug("  . " + cls)
    }

    clauses
  }

  def nextGeneration(gen: Int) = gen + 3

  def decreaseAllGenerations() = {
    for ((block, (gen, origGen, ast, infos)) <- callInfo) {
      // We also decrease the original generation here
      callInfo += block -> (math.max(1,gen-1), math.max(1,origGen-1), ast, infos)
    }

    for ((app, (gen, origGen, b, notB, infos)) <- appInfo) {
      appInfo += app -> (math.max(1,gen-1), math.max(1,origGen-1), b, notB, infos)
    }
  }

  def promoteBlocker(b: T) = {
    if (callInfo contains b) {
      val (_, origGen, ast, fis) = callInfo(b)
      
      callInfo += b -> (1, origGen, ast, fis)
    }

    if (blockerToApp contains b) {
      val app = blockerToApp(b)
      val (_, origGen, _, notB, infos) = appInfo(app)

      appInfo += app -> (1, origGen, b, notB, infos)
    }
  }

  def unrollBehind(ids: Seq[T]): Seq[T] = {
    assert(ids.forall(id => (callInfo contains id) || (blockerToApp contains id)))

    var newClauses : Seq[T] = Seq.empty

    val callInfos = ids.flatMap(id => callInfo.get(id).map(id -> _))
    callInfo = callInfo -- ids

    val apps = ids.flatMap(id => blockerToApp.get(id))
    val appInfos = apps.map(app => app -> appInfo(app))
    blockerToApp = blockerToApp -- ids
    appInfo = appInfo -- apps

    for ((app, (_, _, _, _, infos)) <- appInfos if infos.nonEmpty) {
      val extension = extendAppBlock(app, infos)
      reporter.debug(" -> extending lambda blocker: " + extension)
      newClauses :+= extension
    }

    for ((id, (gen, _, _, infos)) <- callInfos; info @ TemplateCallInfo(tfd, args) <- infos) {
      var newCls = Seq[T]()

      val defBlocker = defBlockers.get(info) match {
        case Some(defBlocker) =>
          // we already have defBlocker => f(args) = body
          defBlocker

        case None =>
          // we need to define this defBlocker and link it to definition
          val defBlocker = encoder.encodeId(FreshIdentifier("d", BooleanType))
          defBlockers += info -> defBlocker

          val template = templateGenerator.mkTemplate(tfd)
          reporter.debug(template)

          val (newExprs, callBlocks, appBlocks) = template.instantiate(defBlocker, args)
          val blockExprs = freshAppBlocks(appBlocks.keys)

          for((b, newInfos) <- callBlocks) {
            registerCallBlocker(nextGeneration(gen), b, newInfos)
          }

          for ((app, newInfos) <- appBlocks) {
            registerAppBlocker(nextGeneration(gen), app, newInfos)
          }

          newCls ++= newExprs
          newCls ++= blockExprs
          defBlocker
      }

      // We connect it to the defBlocker:   blocker => defBlocker
      if (defBlocker != id) {
        newCls ++= List(encoder.mkImplies(id, defBlocker))
      }

      reporter.debug("Unrolling behind "+info+" ("+newCls.size+")")
      for (cl <- newCls) {
        reporter.debug("  . "+cl)
      }

      newClauses ++= newCls
    }

    for ((app @ (b, _), (gen, _, _, _, infos)) <- appInfos; info @ TemplateAppInfo(template, equals, args) <- infos) {
      var newCls = Seq.empty[T]

      val nb = encoder.encodeId(FreshIdentifier("b", BooleanType, true))
      newCls :+= encoder.mkEquals(nb, encoder.mkAnd(equals, b))

      val (newExprs, callBlocks, appBlocks) = template.instantiate(nb, args)
      val blockExprs = freshAppBlocks(appBlocks.keys)

      for ((b, newInfos) <- callBlocks) {
        registerCallBlocker(nextGeneration(gen), b, newInfos)
      }

      for ((newApp, newInfos) <- appBlocks) {
        registerAppBlocker(nextGeneration(gen), newApp, newInfos)
      }

      newCls ++= newExprs
      newCls ++= blockExprs

      reporter.debug("Unrolling behind "+info+" ("+newCls.size+")")
      for (cl <- newCls) {
        reporter.debug("  . "+cl)
      }

      newClauses ++= newCls
    }

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
