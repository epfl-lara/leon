/* Copyright 2009-2015 EPFL, Lausanne */
package leon.xlang

import leon.TransformationPhase
import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.ExprOps._
import leon.purescala.DefOps._
import leon.purescala.Types._
import leon.purescala.Constructors._
import leon.purescala.Extractors._
import leon.xlang.Expressions._

object AntiAliasingPhase extends TransformationPhase {

  val name = "Anti-Aliasing"
  val description = "Make aliasing explicit"

  override def apply(ctx: LeonContext, pgm: Program): Program = {
    val fds = allFunDefs(pgm)
    fds.foreach(fd => checkAliasing(fd)(ctx))

    var updatedFunctions: Map[FunDef, FunDef] = Map()

    val effects = effectsAnalysis(pgm)

    //for each fun def, all the vars the the body captures. Only
    //mutable types.
    val varsInScope: Map[FunDef, Set[Identifier]] = (for {
      fd <- fds
    } yield {
      val allFreeVars = fd.body.map(bd => variablesOf(bd)).getOrElse(Set())
      val freeVars = allFreeVars -- fd.params.map(_.id)
      val mutableFreeVars = freeVars.filter(id => id.getType.isInstanceOf[ArrayType])
      (fd, mutableFreeVars)
    }).toMap

    /*
     * The first pass will introduce all new function definitions,
     * so that in the next pass we can update function invocations
     */
    for {
      fd <- fds
    } {
      updatedFunctions += (fd -> updateFunDef(fd, effects)(ctx))
    }

    for {
      fd <- fds
    } {
      updateBody(fd, effects, updatedFunctions, varsInScope)(ctx)
    }

    val res = replaceFunDefs(pgm)(fd => updatedFunctions.get(fd), (fi, fd) => None)
    //println(res._1)
    res._1
  }

  /*
   * Create a new FunDef for a given FunDef in the program.
   * Adapt the signature to express its effects. In case the
   * function has no effect, this will still introduce a fresh
   * FunDef as the body might have to be updated anyway.
   */
  private def updateFunDef(fd: FunDef, effects: Effects)(ctx: LeonContext): FunDef = {

    val ownEffects = effects(fd)
    val aliasedParams: Seq[Identifier] = fd.params.zipWithIndex.flatMap{
      case (vd, i) if ownEffects.contains(i) => Some(vd)
      case _ => None
    }.map(_.id)

    fd.body.foreach(body => getReturnedExpr(body).foreach{
      case v@Variable(id) if aliasedParams.contains(id) =>
        ctx.reporter.fatalError(v.getPos, "Cannot return a shared reference to a mutable object")
      case _ => ()
    })
    //val allBodies: Set[Expr] = 
    //  fd.body.toSet.flatMap((bd: Expr) => nestedFunDefsOf(bd).flatMap(_.body)) ++ fd.body
    //allBodies.foreach(body => getReturnedExpr(body).foreach{
    //  case v@Variable(id) if aliasedParams.contains(id) =>
    //    ctx.reporter.fatalError(v.getPos, "Cannot return a shared reference to a mutable object: "k+ v)
    //  case _ => ()
    //})

    val newReturnType: TypeTree = if(aliasedParams.isEmpty) fd.returnType else {
      tupleTypeWrap(fd.returnType +: aliasedParams.map(_.getType))
    }
    val newFunDef = new FunDef(fd.id.freshen, fd.tparams, fd.params, newReturnType)
    newFunDef.addFlags(fd.flags)
    newFunDef.setPos(fd)
    newFunDef
  }

  private def updateBody(fd: FunDef, effects: Effects, updatedFunDefs: Map[FunDef, FunDef], varsInScope: Map[FunDef, Set[Identifier]])
                        (ctx: LeonContext): Unit = {

    val ownEffects = effects(fd)
    val aliasedParams: Seq[Identifier] = fd.params.zipWithIndex.flatMap{
      case (vd, i) if ownEffects.contains(i) => Some(vd)
      case _ => None
    }.map(_.id)

    val newFunDef = updatedFunDefs(fd)

    if(aliasedParams.isEmpty) {
      val newBody = fd.body.map(body => {
        makeSideEffectsExplicit(body, Seq(), effects, updatedFunDefs, varsInScope)(ctx)
      })
      newFunDef.body = newBody
      newFunDef.precondition = fd.precondition
      newFunDef.postcondition = fd.postcondition
    } else {
      val freshLocalVars: Seq[Identifier] = aliasedParams.map(v => v.freshen)
      val rewritingMap: Map[Identifier, Identifier] = aliasedParams.zip(freshLocalVars).toMap

      val newBody = fd.body.map(body => {

        val freshBody = replaceFromIDs(rewritingMap.map(p => (p._1, p._2.toVariable)), body) 
        val explicitBody = makeSideEffectsExplicit(freshBody, freshLocalVars, effects, updatedFunDefs, varsInScope)(ctx)

        //WARNING: only works if side effects in Tuples are extracted from left to right,
        //         in the ImperativeTransformation phase.
        val finalBody: Expr = Tuple(explicitBody +: freshLocalVars.map(_.toVariable))

        freshLocalVars.zip(aliasedParams).foldLeft(finalBody)((bd, vp) => {
          LetVar(vp._1, Variable(vp._2), bd)
        })

      })

      val newPostcondition = fd.postcondition.map(post => {
        val Lambda(Seq(res), postBody) = post
        val newRes = ValDef(FreshIdentifier(res.id.name, newFunDef.returnType))
        val newBody =
          replace(
            aliasedParams.zipWithIndex.map{ case (id, i) => 
              (id.toVariable, TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)}.toMap ++
            aliasedParams.map(id =>
              (Old(id), id.toVariable): (Expr, Expr)).toMap +
            (res.toVariable -> TupleSelect(newRes.toVariable, 1)),
          postBody)
        Lambda(Seq(newRes), newBody).setPos(post)
      })

      newFunDef.body = newBody
      newFunDef.precondition = fd.precondition
      newFunDef.postcondition = newPostcondition
    }
  }

  //We turn all local val of mutable objects into vars and explicit side effects
  //using assignments. We also make sure that no aliasing is being done.
  private def makeSideEffectsExplicit
                (body: Expr, aliasedParams: Seq[Identifier], effects: Effects, updatedFunDefs: Map[FunDef, FunDef], varsInScope: Map[FunDef, Set[Identifier]])
                (ctx: LeonContext): Expr = {
    preMapWithContext[Set[Identifier]]((expr, bindings) => expr match {

      case up@ArrayUpdate(a, i, v) => {
        val ra@Variable(id) = a
        if(bindings.contains(id))
          (Some(Assignment(id, ArrayUpdated(ra, i, v).setPos(up)).setPos(up)), bindings)
        else
          (None, bindings)
      }

      case l@Let(id, IsTyped(v, ArrayType(_)), b) => {
        val varDecl = LetVar(id, v, b).setPos(l)
        (Some(varDecl), bindings + id)
      }

      case l@LetVar(id, IsTyped(v, ArrayType(_)), b) => {
        (None, bindings + id)
      }

      //we need to replace local fundef by the new updated fun defs.
      case l@LetDef(fds, body) => { 
        //this might be traversed several time in case of doubly nested fundef,
        //so we need to ignore the second times by checking if updatedFunDefs 
        //contains a mapping or not
        val nfds = fds.map(fd => updatedFunDefs.get(fd).getOrElse(fd))
        (Some(LetDef(nfds, body)), bindings)
      }

      case fi@FunctionInvocation(fd, args) => {

        val vis: Set[Identifier] = varsInScope.get(fd.fd).getOrElse(Set())
        args.find({
          case Variable(id) => vis.contains(id)
          case _ => false
        }).foreach(aliasedArg =>
          ctx.reporter.fatalError(aliasedArg.getPos, "Illegal passing of aliased parameter: " + aliasedArg))

        updatedFunDefs.get(fd.fd) match {
          case None => (None, bindings)
          case Some(nfd) => {
            val nfi = FunctionInvocation(nfd.typed(fd.tps), args).setPos(fi)
            val fiEffects = effects.getOrElse(fd.fd, Set())
            if(fiEffects.nonEmpty) {
              val modifiedArgs: Seq[Variable] = 
                args.zipWithIndex.filter{ case (arg, i) => fiEffects.contains(i) }
                    .map(_._1.asInstanceOf[Variable])

              val duplicatedParams = modifiedArgs.diff(modifiedArgs.distinct).distinct
              if(duplicatedParams.nonEmpty) 
                ctx.reporter.fatalError(fi.getPos, "Illegal passing of aliased parameter: " + duplicatedParams.head)

              val freshRes = FreshIdentifier("res", nfd.returnType)

              val extractResults = Block(
                modifiedArgs.zipWithIndex.map(p => Assignment(p._1.id, TupleSelect(freshRes.toVariable, p._2 + 2))),
                TupleSelect(freshRes.toVariable, 1))


              val newExpr = Let(freshRes, nfi, extractResults)
              (Some(newExpr), bindings)
            } else {
              (Some(nfi), bindings)
            }
          }
        }
      }

      case _ => (None, bindings)

    })(body, aliasedParams.toSet)
  }

  //TODO: in the future, any object with vars could be aliased and so
  //      we will need a general property

  private type Effects = Map[FunDef, Set[Int]]

  /*
   * compute effects for each function in the program, including any nested
   * functions (LetDef).
   */
  private def effectsAnalysis(pgm: Program): Effects = {

    //currently computed effects (incremental)
    var effects: Map[FunDef, Set[Int]] = Map()
    //missing dependencies for a function for its effects to be complete
    var missingEffects: Map[FunDef, Set[FunctionInvocation]] = Map()

    def effectsFullyComputed(fd: FunDef): Boolean = !missingEffects.isDefinedAt(fd)

    for {
      fd <- allFunDefs(pgm)
    } {
      fd.body match {
        case None =>
          effects += (fd -> Set())
        case Some(body) => {
          val mutableParams = fd.params.filter(vd => vd.getType match {
            case ArrayType(_) => true
            case _ => false
          })
          val mutatedParams = mutableParams.filter(vd => exists {
            case ArrayUpdate(Variable(a), _, _) => a == vd.id
            case _ => false
          }(body))
          val mutatedParamsIndices = fd.params.zipWithIndex.flatMap{
            case (vd, i) if mutatedParams.contains(vd) => Some(i)
            case _ => None
          }.toSet
          effects = effects + (fd -> mutatedParamsIndices)

          val missingCalls: Set[FunctionInvocation] = functionCallsOf(body).filterNot(fi => fi.tfd.fd == fd)
          if(missingCalls.nonEmpty)
            missingEffects += (fd -> missingCalls)
        }
      }
    }

    def rec(): Unit = {
      val previousMissingEffects = missingEffects

      for{ (fd, calls) <- missingEffects } {
        var newMissingCalls: Set[FunctionInvocation] = calls
        for(fi <- calls) {
          val mutatedArgs = invocEffects(fi)
          val mutatedFunParams: Set[Int] = fd.params.zipWithIndex.flatMap{
            case (vd, i) if mutatedArgs.contains(vd.id) => Some(i)
            case _ => None
          }.toSet
          effects += (fd -> (effects(fd) ++ mutatedFunParams))

          if(effectsFullyComputed(fi.tfd.fd)) {
            newMissingCalls -= fi
          }
        }
        if(newMissingCalls.isEmpty)
          missingEffects = missingEffects - fd
        else
          missingEffects += (fd -> newMissingCalls)
      }

      if(missingEffects != previousMissingEffects) {
        rec()
      }
    }

    def invocEffects(fi: FunctionInvocation): Set[Identifier] = {
      //TODO: the require should be fine once we consider nested functions as well
      //require(effects.isDefinedAt(fi.tfd.fd)
      val mutatedParams: Set[Int] = effects.get(fi.tfd.fd).getOrElse(Set())
      fi.args.zipWithIndex.flatMap{
        case (Variable(id), i) if mutatedParams.contains(i) => Some(id)
        case _ => None
      }.toSet
    }

    rec()
    effects
  }


  def checkAliasing(fd: FunDef)(ctx: LeonContext): Unit = {
    def checkReturnValue(body: Expr, bindings: Set[Identifier]): Unit = {
      getReturnedExpr(body).foreach{
        case IsTyped(v@Variable(id), ArrayType(_)) if bindings.contains(id) =>
          ctx.reporter.fatalError(v.getPos, "Cannot return a shared reference to a mutable object: " + v)
        case _ => ()
      }
    }
    
    fd.body.foreach(bd => {
      val params = fd.params.map(_.id).toSet
      checkReturnValue(bd, params)
      preMapWithContext[Set[Identifier]]((expr, bindings) => expr match {
        case l@Let(id, IsTyped(v, ArrayType(_)), b) => {
          v match {
            case FiniteArray(_, _, _) => ()
            case FunctionInvocation(_, _) => ()
            case _ => ctx.reporter.fatalError(l.getPos, "Cannot alias array: " + l)
          }
          (None, bindings + id)
        }
        case l@LetVar(id, IsTyped(v, ArrayType(_)), b) => {
          v match {
            case FiniteArray(_, _, _) => ()
            case FunctionInvocation(_, _) => ()
            case _ => ctx.reporter.fatalError(l.getPos, "Cannot alias array: " + l)
          }
          (None, bindings + id)
        }
        case l@LetDef(fds, body) => {
          fds.foreach(fd => fd.body.foreach(bd => checkReturnValue(bd, bindings)))
          (None, bindings)
        }

        case _ => (None, bindings)
      })(bd, params)
    })
  }

  /*
   * A bit hacky, but not sure of the best way to do something like that
   * currently.
   */
  private def getReturnedExpr(expr: Expr): Seq[Expr] = expr match {
    case Let(_, _, rest) => getReturnedExpr(rest)
    case LetVar(_, _, rest) => getReturnedExpr(rest)
    case Block(_, rest) => getReturnedExpr(rest)
    case IfExpr(_, thenn, elze) => getReturnedExpr(thenn) ++ getReturnedExpr(elze)
    case MatchExpr(_, cses) => cses.flatMap{ cse => getReturnedExpr(cse.rhs) }
    case e => Seq(expr)
  }


  /*
   * returns all fun def in the program, including local definitions inside
   * other functions (LetDef).
   */
  private def allFunDefs(pgm: Program): Seq[FunDef] =
      pgm.definedFunctions.flatMap(fd => 
        fd.body.toSet.flatMap((bd: Expr) =>
          nestedFunDefsOf(bd)) + fd)
}
