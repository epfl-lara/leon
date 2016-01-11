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

    var updatedFunctions: Map[FunDef, (FunDef, Seq[ValDef])] = Map()

    println("effects: " + effectsAnalysis(pgm).filter(p => p._2.size > 0).map(p => p._1.id + ": " + p._2))

    for {
      fd <- pgm.definedFunctions
    } {
      updateFunDef(fd)(ctx).foreach{ case (nfd, mvs) => {
        updatedFunctions += (fd -> ((nfd, mvs)))
      }}
    }

    //println(updatedFunctions)

    for {
      fd <- pgm.definedFunctions
    } {
      fd.body = fd.body.map(bd => updateInvocations(bd, updatedFunctions)(ctx))
    }

    val res = replaceFunDefs(pgm)(fd => updatedFunctions.get(fd).map(_._1), (fi, fd) => None)
    //println(res._1)
    res._1
  }

  private def updateInvocations(body: Expr, updatedFunctions: Map[FunDef, (FunDef, Seq[ValDef])])(ctx: LeonContext): Expr = {
    val freshBody = postMap {
      case fi@FunctionInvocation(fd, args) => updatedFunctions.get(fd.fd).map{ case (nfd, modifiedParams) => {
        val modifiedArgs: Seq[Variable] = 
          args.zip(fd.params)
              .filter(p => modifiedParams.contains(p._2))
              .map(_._1.asInstanceOf[Variable])

        val freshRes = FreshIdentifier("res", nfd.returnType)

        val extractResults = Block(
          modifiedArgs.zipWithIndex.map(p => Assignment(p._1.id, TupleSelect(freshRes.toVariable, p._2 + 2))),
          TupleSelect(freshRes.toVariable, 1))


        Let(freshRes, FunctionInvocation(nfd.typed, args).setPos(fi), extractResults)
      }}
      case _ => None
    }(body)

    freshBody
  }

  private def updateFunDef(fd: FunDef)(ctx: LeonContext): Option[(FunDef, Seq[ValDef])] = {
    val aliasedParams: Seq[Identifier] = 
      fd.params.filter(vd => vd.getType match {
        case ArrayType(_) => {
          fd.body.exists(body => {
            exists{
              case ArrayUpdate(Variable(a), _, _) => a == vd.id
              case _ => false
            }(body)
          })
        }
        case _ => false
      }).map(_.id)


    val explicitBody = fd.body.map(bd => makeSideEffectsExplicit(bd, aliasedParams)(ctx))

    if(aliasedParams.isEmpty) {
      None
    } else {
      val freshLocalVars: Seq[Identifier] = aliasedParams.map(v => v.freshen)
      val rewritingMap: Map[Identifier, Identifier] = aliasedParams.zip(freshLocalVars).toMap

      val newBody = fd.body.map(body => {

        //val freshBody = postMap {
        //  case au@ArrayUpdate(a, i, v) =>
        //    val Variable(id) = a
        //    rewritingMap.get(id).map(freshId =>
        //      Assignment(freshId, ArrayUpdated(freshId.toVariable, i, v).setPos(au)).setPos(au)
        //    )
        //  case _ => None
        //  //case as@ArraySelect(a, i) =>

        //  //case l@Let(i, IsTyped(v, ArrayType(_)), b) =>
        //  //  LetVar(i, v, b).setPos(l)
        //}(body)

        val freshBody = replaceFromIDs(rewritingMap.map(p => (p._1, p._2.toVariable)), body) 

        //WARNING: only works if side effects in Tuples are extracted from left to right,
        //         in the ImperativeTransformation phase.
        val finalBody: Expr = Tuple(freshBody +: freshLocalVars.map(_.toVariable))

        freshLocalVars.zip(aliasedParams).foldLeft(finalBody)((bd, vp) => {
          Let(vp._1, Variable(vp._2), bd)
        })

      })

      val newReturnType: TypeTree = {
        tupleTypeWrap(fd.returnType +: freshLocalVars.map(_.getType))
      }

      val newPostcondition = fd.postcondition.map(post => {
        val Lambda(Seq(res), postBody) = post
        val newRes = ValDef(FreshIdentifier(res.id.name, newReturnType))
        val newBody =
          replace(
            aliasedParams.zipWithIndex.map{ case (id, i) => 
              (id.toVariable, TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)}.toMap +
            (res.toVariable -> TupleSelect(newRes.toVariable, 1)),
          postBody)
        Lambda(Seq(newRes), newBody).setPos(post)
      })

      val newFunDef = new FunDef(fd.id.freshen, fd.tparams, fd.params, newReturnType)
      newFunDef.addFlags(fd.flags)
      newFunDef.setPos(fd)
      newFunDef.body = newBody
      newFunDef.precondition = fd.precondition
      newFunDef.postcondition = newPostcondition

      Some((newFunDef, aliasedParams.map(id => ValDef(id))))
    }
  }

  //We turn all local val of mutable objects into vars and explicit side effects
  //using assignments. We also make sure that no aliasing is being done.
  private def makeSideEffectsExplicit(body: Expr, aliasedParams: Seq[Identifier])(ctx: LeonContext): Expr = {
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
        
      case _ => (None, bindings)
    })(body, Set())
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
      body <- fd.body
    } {

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
      val mutatedParams: Set[Int] = effects(fi.tfd.fd)
      fi.args.zipWithIndex.flatMap{
        case (Variable(id), i) if mutatedParams.contains(i) => Some(id)
        case _ => None
      }.toSet
    }


    rec()
    effects
  }


}
