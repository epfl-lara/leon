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

    var updatedFunctions: Map[FunDef, FunDef] = Map()

    val effects = effectsAnalysis(pgm)

    /*
     * The first pass will introduce all new function definitions,
     * so that in the next pass we can update function invocations
     */
    for {
      fd <- pgm.definedFunctions
    } {
      updatedFunctions += (fd -> updateFunDef(fd, effects)(ctx))
    }

    for {
      fd <- pgm.definedFunctions
    } {
      updateBody(fd, effects, updatedFunctions)(ctx)
    }

    val res = replaceFunDefs(pgm)(fd => updatedFunctions.get(fd), (fi, fd) => None)
    println(res._1)
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

    val newReturnType: TypeTree = if(aliasedParams.isEmpty) fd.returnType else {
      tupleTypeWrap(fd.returnType +: aliasedParams.map(_.getType))
    }
    val newFunDef = new FunDef(fd.id.freshen, fd.tparams, fd.params, newReturnType)
    newFunDef.addFlags(fd.flags)
    newFunDef.setPos(fd)
    newFunDef
  }

  private def updateBody(fd: FunDef, effects: Effects, updatedFunDefs: Map[FunDef, FunDef])
                        (ctx: LeonContext): Unit = {

    val ownEffects = effects(fd)
    val aliasedParams: Seq[Identifier] = fd.params.zipWithIndex.flatMap{
      case (vd, i) if ownEffects.contains(i) => Some(vd)
      case _ => None
    }.map(_.id)

    val newFunDef = updatedFunDefs(fd)

    if(aliasedParams.isEmpty) {
      val newBody = fd.body.map(body => {
        makeSideEffectsExplicit(body, Seq(), effects, updatedFunDefs)(ctx)
      })
      newFunDef.body = newBody
      newFunDef.precondition = fd.precondition
      newFunDef.postcondition = fd.postcondition
    } else {
      val freshLocalVars: Seq[Identifier] = aliasedParams.map(v => v.freshen)
      val rewritingMap: Map[Identifier, Identifier] = aliasedParams.zip(freshLocalVars).toMap

      val newBody = fd.body.map(body => {

        val freshBody = replaceFromIDs(rewritingMap.map(p => (p._1, p._2.toVariable)), body) 
        val explicitBody = makeSideEffectsExplicit(freshBody, freshLocalVars, effects, updatedFunDefs)(ctx)

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
              (id.toVariable, TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)}.toMap +
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
                (body: Expr, aliasedParams: Seq[Identifier], effects: Effects, updatedFunDefs: Map[FunDef, FunDef])
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
        v match {
          case FiniteArray(_, _, _) => ()
          case FunctionInvocation(_, _) => ()
          case _ => ctx.reporter.fatalError(l.getPos, "Cannot alias array")
        }

        val varDecl = LetVar(id, v, b).setPos(l)
        (Some(varDecl), bindings + id)
      }

      case l@LetVar(id, IsTyped(v, ArrayType(_)), b) => {
        v match {
          case FiniteArray(_, _, _) => ()
          case FunctionInvocation(_, _) => ()
          case _ => ctx.reporter.fatalError(l.getPos, "Cannot alias array")
        }

        (None, bindings + id)
      }

      case fi@FunctionInvocation(fd, args) => {
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

  private def effectsAnalysis(pgm: Program): Effects = {

    //currently computed effects (incremental)
    var effects: Map[FunDef, Set[Int]] = Map()
    //missing dependencies for a function for its effects to be complete
    var missingEffects: Map[FunDef, Set[FunctionInvocation]] = Map()

    def effectsFullyComputed(fd: FunDef): Boolean = !missingEffects.isDefinedAt(fd)

    for {
      fd <- pgm.definedFunctions
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
      if(!effects.isDefinedAt(fi.tfd.fd)) {
        println("fi not defined: " + fi)
      }
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

}
