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
import leon.purescala.DependencyFinder
import leon.purescala.DefinitionTransformer
import leon.utils.Bijection
import leon.xlang.Expressions._
import leon.xlang.ExprOps._

object AntiAliasingPhase extends TransformationPhase {

  val name = "Anti-Aliasing"
  val description = "Make aliasing explicit"


  override def apply(ctx: LeonContext, program: Program): Program = {

    //mapping for case classes that needs to be replaced
    //var ccdMap: Map[CaseClassDef, CaseClassDef] =
    //  (for {
    //    ccd <- program.singleCaseClasses
    //  } yield (ccd, updateCaseClassDef(ccd))).toMap.filter(p => p._1 != p._2)


    //println("ccdMap: " + ccdMap)
    //val ccdBijection: Bijection[ClassDef, ClassDef] = Bijection(ccdMap)
    //val (pgm, _, _, _) = replaceDefs(program)(fd => None, cd => ccdBijection.getB(cd))
    //println(pgm)

    //val dependencies = new DependencyFinder
    //ccdMap = updateCaseClassDefs(ccdMap, dependencies, pgm)

    //val idsMap: Map[Identifier, Identifier] = ccdMap.flatMap(p => {
    //  p._1.fields.zip(p._2.fields).filter(pvd => pvd._1.id != pvd._2).map(p => (p._1.id, p._2.id))
    //}).toMap
    val transformer = new DefinitionTransformer {
      override def transformType(tpe: TypeTree): Option[TypeTree] = tpe match {
        case (ft: FunctionType) => Some(makeFunctionTypeExplicit(ft))
        case _ => None
      }
      //override def transformClassDef(cd: ClassDef): Option[ClassDef] = ccdBijection.getB(cd)
    }
    //pgm.singleCaseClasses.foreach(ccd => println(ccd + " -> " + defTf.transform(ccd)))
    val cdsMap = program.definedClasses.map(cd => cd -> transformer.transform(cd)).toMap
    val fdsMap = program.definedFunctions.map(fd => fd -> transformer.transform(fd)).toMap
    val pgm = replaceDefsInProgram(program)(fdsMap, cdsMap)
    //println(leon.purescala.ScalaPrinter(pgm, ctx))//leon.purescala.ScalaPrinter.create(leon.purescala.PrinterOptions(printTypes = true), Some(pgm)).pp(pgm))
    //println(pgm)

    val fds = allFunDefs(pgm)
    fds.foreach(fd => checkAliasing(fd)(ctx))

    var updatedFunctions: Map[FunDef, FunDef] = Map()

    val effects = effectsAnalysis(pgm)
    //println("effects: " + effects.filter(e => e._2.size > 0).map(e => (e._1.id, e._2)))

    //for each fun def, all the vars the the body captures. Only
    //mutable types.
    val varsInScope: Map[FunDef, Set[Identifier]] = (for {
      fd <- fds
    } yield {
      val allFreeVars = fd.body.map(bd => variablesOf(bd)).getOrElse(Set())
      val freeVars = allFreeVars -- fd.params.map(_.id)
      val mutableFreeVars = freeVars.filter(id => isMutableType(id.getType))
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
    //println(updatedFunctions.filter(p => p._1.id != p._2.id).mkString("\n"))

    for {
      fd <- fds
    } {
      updateBody(fd, effects, updatedFunctions, varsInScope)(ctx)
    }

    replaceDefsInProgram(pgm)(updatedFunctions, Map[ClassDef, ClassDef]())

    //pgm.copy(units = for (u <- pgm.units) yield {
    //  u.copy(defs = u.defs.map {
    //    case m : ModuleDef =>
    //      m.copy(defs = for (df <- m.defs) yield {
    //        df match {
    //          case cd : CaseClassDef => ccdBijection.getBorElse(cd, cd)
    //          case fd : FunDef => updatedFunctions.getOrElse(fd, fd)
    //          case d => d
    //        }
    //    })
    //    case cd: CaseClassDef => ccdBijection.getBorElse(cd, cd)
    //    case d => d
    //  })
    //})
  }

  /*
   * Create a new FunDef for a given FunDef in the program.
   * Adapt the signature to express its effects. In case the
   * function has no effect, this will still return the original
   * fundef.
   *
   * Also update FunctionType parameters that need to become explicit
   * about the effect they could perform (returning any mutable type that
   * they receive).
   */
  private def updateFunDef(fd: FunDef, effects: Effects)(ctx: LeonContext): FunDef = {

    val ownEffects = effects(fd)
    val aliasedParams: Seq[Identifier] = fd.params.zipWithIndex.flatMap{
      case (vd, i) if ownEffects.contains(i) => Some(vd)
      case _ => None
    }.map(_.id)

    //val newParams = fd.params.map(vd => vd.getType match {
    //  case (ft: FunctionType) => {
    //    val nft = makeFunctionTypeExplicit(ft)
    //    if(ft == nft) vd else ValDef(vd.id.duplicate(tpe = nft))
    //  }
    //  case (cct: CaseClassType) => ccdMap.get(cct.classDef) match {
    //    case Some(ncd) => ValDef(vd.id.duplicate(tpe = ncd.typed))
    //    case None => vd
    //  }
    //  case _ => vd
    //})


    fd.body.foreach(body => getReturnedExpr(body).foreach{
      case v@Variable(id) if aliasedParams.contains(id) =>
        ctx.reporter.fatalError(v.getPos, "Cannot return a shared reference to a mutable object")
      case _ => ()
    })

    if(aliasedParams.isEmpty) fd else {
      val newReturnType: TypeTree = tupleTypeWrap(fd.returnType +: aliasedParams.map(_.getType))
      val newFunDef = new FunDef(fd.id.freshen, fd.tparams, fd.params, newReturnType)
      newFunDef.addFlags(fd.flags)
      newFunDef.setPos(fd)
      newFunDef
    }
  }

  //private def updateCaseClassDef(ccd: CaseClassDef): CaseClassDef = {
  //  val newFields = ccd.fields.map(vd => vd.getType match {
  //    case (ft: FunctionType) => {
  //      val nft = makeFunctionTypeExplicit(ft)
  //      if(nft == ft) vd else {
  //        ValDef(vd.id.duplicate(tpe = nft))
  //      }
  //    }
  //    case _ => vd
  //  })
  //  if(newFields != ccd.fields) {
  //    ccd.duplicate(fields = newFields)
  //  } else {
  //    ccd
  //  }
  //}

  //recursively update until fixpoint reach
  //private def updateCaseClassDefs(ccdMap: Map[CaseClassDef, CaseClassDef], deps: DependencyFinder, pgm: Program): Map[CaseClassDef, CaseClassDef] = {
  //  for {
  //    ccd <- pgm.singleCaseClasses
  //  } {
  //    if(deps(ccd).exists(_ ==
  //    (ccd, updateCaseClassDef(ccd))).toMap.filter(p => p._1 != p._2) 
  //  }
  //  for
  //}

  private def updateBody(fd: FunDef, effects: Effects, updatedFunDefs: Map[FunDef, FunDef], 
                         varsInScope: Map[FunDef, Set[Identifier]])
                        (ctx: LeonContext): Unit = {
    //println("updating: " + fd)

    val ownEffects = effects(fd)
    val aliasedParams: Seq[Identifier] = fd.params.zipWithIndex.flatMap{
      case (vd, i) if ownEffects.contains(i) => Some(vd)
      case _ => None
    }.map(_.id)

    val newFunDef = updatedFunDefs(fd)

    if(aliasedParams.isEmpty) {
      val newBody = fd.body.map(body => {
        makeSideEffectsExplicit(body, fd, Seq(), effects, updatedFunDefs, varsInScope)(ctx)
      })
      newFunDef.body = newBody
      newFunDef.precondition = fd.precondition
      newFunDef.postcondition = fd.postcondition
    } else {
      val freshLocalVars: Seq[Identifier] = aliasedParams.map(v => v.freshen)
      val rewritingMap: Map[Identifier, Identifier] = aliasedParams.zip(freshLocalVars).toMap

      val newBody = fd.body.map(body => {

        val freshBody = rewriteIDs(rewritingMap, body)
        val explicitBody = makeSideEffectsExplicit(freshBody, fd, freshLocalVars, effects, updatedFunDefs, varsInScope)(ctx)

        //only now we rewrite function parameters that changed names when the new function was introduced
        val paramRewritings: Map[Identifier, Identifier] =
          fd.params.zip(newFunDef.params).filter({
            case (ValDef(oid), ValDef(nid)) if oid != nid => true
            case _ => false
          }).map(p => (p._1.id, p._2.id)).toMap
        val explicitBody2 = replaceFromIDs(paramRewritings.map(p => (p._1, p._2.toVariable)), explicitBody)
              

        //WARNING: only works if side effects in Tuples are extracted from left to right,
        //         in the ImperativeTransformation phase.
        val finalBody: Expr = Tuple(explicitBody2 +: freshLocalVars.map(_.toVariable))

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
                (body: Expr, originalFd: FunDef, aliasedParams: Seq[Identifier], effects: Effects, 
                 updatedFunDefs: Map[FunDef, FunDef], varsInScope: Map[FunDef, Set[Identifier]])
                (ctx: LeonContext): Expr = {

    val newFunDef = updatedFunDefs(originalFd)
                  
    def mapApplication(args: Seq[Expr], nfi: Expr, nfiType: TypeTree, fiEffects: Set[Int], rewritings: Map[Identifier, Expr]): Expr = {
      if(fiEffects.nonEmpty) {
        val modifiedArgs: Seq[(Identifier, Expr)] =
          args.zipWithIndex.filter{ case (arg, i) => fiEffects.contains(i) }
              .map(arg => {
                    val rArg = replaceFromIDs(rewritings, arg._1)
                    (findReceiverId(rArg).get, rArg)
                   })

        val duplicatedParams = modifiedArgs.diff(modifiedArgs.distinct).distinct
        if(duplicatedParams.nonEmpty) 
          ctx.reporter.fatalError(nfi.getPos, "Illegal passing of aliased parameter: " + duplicatedParams.head)

        val freshRes = FreshIdentifier("res", nfiType)

        val extractResults = Block(
          modifiedArgs.zipWithIndex.map{ case ((id, expr), index) => {
            val resSelect = TupleSelect(freshRes.toVariable, index + 2)
            expr match {
              case CaseClassSelector(_, obj, mid) =>
                Assignment(id, deepCopy(obj, mid, resSelect))
              case _ =>
                Assignment(id, resSelect)
            }
          }},
          TupleSelect(freshRes.toVariable, 1))


        val newExpr = Let(freshRes, nfi, extractResults)
        newExpr
      } else {
        nfi
      }
    }

    preMapWithContext[(Set[Identifier], Map[Identifier, Expr], Set[Expr])]((expr, context) => {
      val bindings = context._1
      val rewritings = context._2
      val toIgnore = context._3
      expr match {

        case l@Let(id, IsTyped(v, tpe), b) if isMutableType(tpe) => {
          val varDecl = LetVar(id, v, b).setPos(l)
          (Some(varDecl), (bindings + id, rewritings, toIgnore))
        }

        //case l@Let(id, IsTyped(v, CaseClassType(ccd, _)), b) if ccdMap.contains(ccd) => {
        //  val ncd = ccdMap(ccd)
        //  val freshId = id.duplicate(tpe = ncd.typed)
        //  val freshBody = replaceFromIDs(Map(id -> freshId.toVariable), b)
        //  (Some(Let(freshId, v, freshBody).copiedFrom(l)), context)
        //}

        case l@LetVar(id, IsTyped(v, tpe), b) if isMutableType(tpe) => {
          (None, (bindings + id, rewritings, toIgnore))
        }

        case m@MatchExpr(scrut, cses) if isMutableType(scrut.getType) => {

          val tmp: Map[Identifier, Expr] = cses.flatMap{ case MatchCase(pattern, guard, rhs) => {
            mapForPattern(scrut, pattern)
            //val binder = pattern.binder.get
            //binder -> scrut
          }}.toMap

          (None, (bindings, rewritings ++ tmp, toIgnore))
        }

        case up@ArrayUpdate(a, i, v) => {
          val ra@Variable(id) = a
          if(bindings.contains(id))
            (Some(Assignment(id, ArrayUpdated(ra, i, v).setPos(up)).setPos(up)), context)
          else
            (None, context)
        }

        case as@FieldAssignment(o, id, v) => {
          val so = replaceFromIDs(rewritings, o)
          findReceiverId(so) match {
            case None =>
              ctx.reporter.fatalError(as.getPos, "Unsupported form of field assignment: " + as)
            case Some(oid) => {
              if(bindings.contains(oid))
                (Some(Assignment(oid, deepCopy(so, id, v))), context)
              else
                (None, context)
            }
          }
        }

        //we need to replace local fundef by the new updated fun defs.
        case l@LetDef(fds, body) => {
          //this might be traversed several time in case of doubly nested fundef,
          //so we need to ignore the second times by checking if updatedFunDefs 
          //contains a mapping or not
          val nfds = fds.map(fd => updatedFunDefs.get(fd).getOrElse(fd))
          (Some(LetDef(nfds, body).copiedFrom(l)), context)
        }

        case lambda@Lambda(params, body) => {
          val ft@FunctionType(_, _) = lambda.getType
          val ownEffects = functionTypeEffects(ft)
          val aliasedParams: Seq[Identifier] = params.zipWithIndex.flatMap{
            case (vd, i) if ownEffects.contains(i) => Some(vd)
            case _ => None
          }.map(_.id)

          if(aliasedParams.isEmpty) {
            (None, context)
          } else {
            val freshLocalVars: Seq[Identifier] = aliasedParams.map(v => v.freshen)
            val rewritingMap: Map[Identifier, Identifier] = aliasedParams.zip(freshLocalVars).toMap
            val freshBody = replaceFromIDs(rewritingMap.map(p => (p._1, p._2.toVariable)), body) 
            val explicitBody = makeSideEffectsExplicit(freshBody, originalFd, freshLocalVars, effects, updatedFunDefs, varsInScope)(ctx)

            //WARNING: only works if side effects in Tuples are extracted from left to right,
            //         in the ImperativeTransformation phase.
            val finalBody: Expr = Tuple(explicitBody +: freshLocalVars.map(_.toVariable))

            val wrappedBody: Expr = freshLocalVars.zip(aliasedParams).foldLeft(finalBody)((bd, vp) => {
              LetVar(vp._1, Variable(vp._2), bd)
            })
            val finalLambda = Lambda(params, wrappedBody).copiedFrom(lambda)

            (Some(finalLambda), context)
          }

        }

        case fi@FunctionInvocation(fd, args) => {

          val vis: Set[Identifier] = varsInScope.get(fd.fd).getOrElse(Set())
          args.find({
            case Variable(id) => vis.contains(id)
            case _ => false
          }).foreach(aliasedArg =>
            ctx.reporter.fatalError(aliasedArg.getPos, "Illegal passing of aliased parameter: " + aliasedArg))



          updatedFunDefs.get(fd.fd) match {
            case None => (None, context)
            case Some(nfd) => {
              val nfi = FunctionInvocation(nfd.typed(fd.tps), args.map(arg => replaceFromIDs(rewritings, arg))).copiedFrom(fi)
              val fiEffects = effects.getOrElse(fd.fd, Set())
              (Some(mapApplication(args, nfi, nfd.typed(fd.tps).returnType, fiEffects, rewritings)), context)
            }
          }
        }

        case app@Application(callee, args) => {
          if(toIgnore(app)) (None, context) else {
            val ft@FunctionType(_, to) = callee.getType
            to match {
              case TupleType(tps) if isMutableType(tps.last) => {
                val nfi = Application(callee, args.map(arg => replaceFromIDs(rewritings, arg))).copiedFrom(app)
                val fiEffects = functionTypeEffects(ft)
                (Some(mapApplication(args, nfi, to, fiEffects, rewritings)), (bindings, rewritings, toIgnore + nfi))
              }
              case _ => (None, context)
            }
          }
        }

        //case app@Application(callee@Variable(id), args) => {
        //  originalFd.params.zip(newFunDef.params)
        //                   .find(p => p._1.id == id)
        //                   .map(p => p._2.id) match {
        //    case Some(newId) =>
        //      val ft@FunctionType(_, _) = callee.getType
        //      val nft = makeFunctionTypeExplicit(ft)

        //      if(ft == nft) (None, context) else {
        //        val nfi = Application(Variable(newId).copiedFrom(callee), args.map(arg => replaceFromIDs(rewritings, arg))).copiedFrom(app)
        //        val fiEffects = functionTypeEffects(ft)
        //        (Some(mapApplication(args, nfi, nft.to, fiEffects, rewritings)), context)
        //      }
        //    case None => (None, context)
        //  }
        //}

        //case app@Application(callee@CaseClassSelector(cct, obj, id), args) => {
        //  ccdMap.get(cct.classDef) match {
        //    case None =>
        //      (None, context)
        //    case Some(ncd) => {
        //      val nid = cct.classDef.fields.zip(ncd.fields).find(p => id == p._1.id).map(_._2.id).get
        //      val nccs = CaseClassSelector(ncd.typed, obj, nid).copiedFrom(callee)
        //      val nfi = Application(nccs, args.map(arg => replaceFromIDs(rewritings, arg))).copiedFrom(app)
        //      val ft@FunctionType(_, _) = callee.getType
        //      val nft = makeFunctionTypeExplicit(ft)
        //      val fiEffects = functionTypeEffects(ft)
        //      (Some(mapApplication(args, nfi, nft.to, fiEffects, rewritings)), context)
        //    }
        //  }
        //}

        //case CaseClass(cct, args) => {
        //  ccdMap.get(cct.classDef) match {
        //    case None =>
        //      (None, context)
        //    case Some(ncd) => {
        //      (Some(CaseClass(ncd.typed, args)), context)
        //    }
        //  }
        //}

        case _ => (None, context)
      }

    })(body, (aliasedParams.toSet, Map(), Set()))
  }

  //for each fundef, the set of modified params (by index)
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
          val mutableParams = fd.params.filter(vd => isMutableType(vd.getType))
          val localAliases: Map[ValDef, Set[Identifier]] = mutableParams.map(vd => (vd, computeLocalAliases(vd.id, body))).toMap
          val mutatedParams = mutableParams.filter(vd => exists(expr => localAliases(vd).exists(id => isMutationOf(expr, id)))(body))
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
      functionInvocationEffects(fi, mutatedParams).toSet
    }

    rec()
    effects
  }

  //convert a function type with mutable parameters, into a function type
  //that returns the mutable parameters. This makes explicit all possible
  //effects of the function. This should be used for higher order functions
  //declared as parameters.
  def makeFunctionTypeExplicit(tpe: FunctionType): FunctionType = {
    val newReturnTypes = tpe.from.filter(t => isMutableType(t))
    if(newReturnTypes.isEmpty)
      tpe
    else {
      FunctionType(tpe.from, TupleType(tpe.to +: newReturnTypes))
    }
  }

  def functionTypeEffects(ft: FunctionType): Set[Int] = {
    ft.from.zipWithIndex.flatMap{ case (vd, i) =>
      if(isMutableType(vd.getType)) Some(i) else None
    }.toSet
  }

  //for a given id, compute the identifiers that alias it or some part of the object refered by id
  def computeLocalAliases(id: Identifier, body: Expr): Set[Identifier] = {
    def pre(expr: Expr, ids: Set[Identifier]): Set[Identifier] = expr match {
      case l@Let(i, Variable(v), _) if ids.contains(v) => ids + i
      case m@MatchExpr(Variable(v), cses) if ids.contains(v) => {
        val newIds = cses.flatMap(mc => mc.pattern.binders)
        ids ++ newIds
      }
      case e => ids
    }
    def combiner(e: Expr, ctx: Set[Identifier], ids: Seq[Set[Identifier]]): Set[Identifier] = ctx ++ ids.toSet.flatten + id
    val res = preFoldWithContext(pre, combiner)(body, Set(id))
    res
  }


  def checkAliasing(fd: FunDef)(ctx: LeonContext): Unit = {
    def checkReturnValue(body: Expr, bindings: Set[Identifier]): Unit = {
      getReturnedExpr(body).foreach{
        case expr if isMutableType(expr.getType) => 
          findReceiverId(expr).foreach(id =>
            if(bindings.contains(id))
              ctx.reporter.fatalError(expr.getPos, "Cannot return a shared reference to a mutable object: " + expr)
          )
        case _ => ()
      }
    }
    
    fd.body.foreach(bd => {
      val params = fd.params.map(_.id).toSet
      checkReturnValue(bd, params)
      preMapWithContext[Set[Identifier]]((expr, bindings) => expr match {
        case l@Let(id, v, b) if isMutableType(v.getType) => {
          v match {
            case FiniteArray(_, _, _) => ()
            case FunctionInvocation(_, _) => ()
            case ArrayUpdated(_, _, _) => ()
            case CaseClass(_, _) => ()
            case _ => ctx.reporter.fatalError(v.getPos, "Illegal aliasing: " + v)
          }
          (None, bindings + id)
        }
        case l@LetVar(id, v, b) if isMutableType(v.getType) => {
          v match {
            case FiniteArray(_, _, _) => ()
            case FunctionInvocation(_, _) => ()
            case ArrayUpdated(_, _, _) => ()
            case CaseClass(_, _) => ()
            case _ => ctx.reporter.fatalError(v.getPos, "Illegal aliasing: " + v)
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


  private def findReceiverId(o: Expr): Option[Identifier] = o match {
    case Variable(id) => Some(id)
    case CaseClassSelector(_, e, _) => findReceiverId(e)
    case AsInstanceOf(e, ct) => findReceiverId(e)
    case _ => None
  }


  private def isMutableType(tpe: TypeTree, abstractClasses: Set[ClassType] = Set()): Boolean = tpe match {
    case (ct: ClassType) if abstractClasses.contains(ct) => false
    case (arr: ArrayType) => true
    case ct@CaseClassType(ccd, _) => ccd.fields.exists(vd => vd.isVar || isMutableType(vd.getType, abstractClasses + ct))
    case (ct: ClassType) => ct.knownDescendants.exists(c => isMutableType(c, abstractClasses + ct))
    case _ => false
  }


  /*
   * Check if expr is mutating variable id
   */
  private def isMutationOf(expr: Expr, id: Identifier): Boolean = expr match {
    case ArrayUpdate(Variable(a), _, _) => a == id
    case FieldAssignment(obj, _, _) => findReceiverId(obj).exists(_ == id)
    case Application(callee, args) => {
      val ft@FunctionType(_, _) = callee.getType
      val effects = functionTypeEffects(ft)
      args.zipWithIndex.exists{
        case (Variable(argId), index) => argId == id && effects.contains(index)
        case _ => false
      }
    }
    case _ => false
  }

  //return the set of modified variables arguments to a function invocation,
  //given the effect of the fun def invoked.
  private def functionInvocationEffects(fi: FunctionInvocation, effects: Set[Int]): Seq[Identifier] = {
    fi.args.map(arg => findReceiverId(arg)).zipWithIndex.flatMap{
      case (Some(id), i) if effects.contains(i) => Some(id)
      case _ => None
    }
  }

  //private def extractFieldPath(o: Expr): (Expr, List[Identifier]) = {
  //  def rec(o: Expr): List[Identifier] = o match {
  //    case CaseClassSelector(_, r, i) =>
  //      val res = toFieldPath(r)
  //      (res._1, i::res)
  //    case expr => (expr, Nil)
  //  }
  //  val res = rec(o)
  //  (res._1, res._2.reverse)
  //}

  private def deepCopy(rec: Expr, id: Identifier, nv: Expr): Expr = {
    val sub = copy(rec, id, nv)
    rec match {
      case CaseClassSelector(_, r, i) =>
        deepCopy(r, i, sub)
      case expr => sub
    }
  }

  private def copy(cc: Expr, id: Identifier, nv: Expr): Expr = {
    val ct@CaseClassType(ccd, _) = cc.getType
    val newFields = ccd.fields.map(vd =>
      if(vd.id == id)
        nv
      else
        CaseClassSelector(CaseClassType(ct.classDef, ct.tps), cc, vd.id)
    )
    CaseClass(CaseClassType(ct.classDef, ct.tps), newFields).setPos(cc.getPos)
  }

}
